import Acorn.Digits
import Acorn.Host.Viewer.Broadcast
import Acorn.Host.Viewer.ControlRequest
import Acorn.Host.Viewer.RunDirectory
import Acorn.Host.Viewer.ServerView
import Acorn.Host.Viewer.StageBmp
import Std.Http.Server

namespace Acorn.Host.Viewer
open Std Async Http

inductive ControlResult where
  | accepted
  | unavailable
  | busy
  | clearUnavailable
  | refused (reason : String)
  | unconfirmed (reason : String)
  deriving Nonempty

inductive ControlDispatch where
  | immediate (result : ControlResult)
  | pending (task : Task (Option ControlResult))

structure ViewerAssets where
  stylesheet : String

structure HttpViewer where
  private mk ::
  private broadcast : Broadcast
  private token : String
  private assets : ViewerAssets
  private submit : Command → BaseIO ControlDispatch

def HttpViewer.new (broadcast : Broadcast) (assets : ViewerAssets)
    (submit : Command → BaseIO ControlDispatch) : IO HttpViewer := do
  return ⟨broadcast, ← mintControlToken, assets, submit⟩

private def singleHeader (head : Request.Head) (name : Header.Name) : Option String := do
  let values ← head.headers.getAll? name
  if size : values.size = 1 then return (values[0]'(by omega)).value else none

private def controlHeaders (head : Request.Head) : ControlHeaders :=
  let contentType := (singleHeader head (.mk "content-type")).getD ""
  let mediaType := ((contentType.splitOn ";").headD "").trimAscii.toString.toLower
  let length := (singleHeader head (.mk "content-length")).bind Digits.read
  ⟨toString head.method, mediaType, (singleHeader head (.mk "x-oak-token")).getD "", length⟩

private def formControlHeaders (head : Request.Head) : FormControlHeaders :=
  let contentType := (singleHeader head (.mk "content-type")).getD ""
  let mediaType := ((contentType.splitOn ";").headD "").trimAscii.toString.toLower
  let length := (singleHeader head (.mk "content-length")).bind Digits.read
  ⟨toString head.method, mediaType, length⟩

private def response (status : Status) (contentType : Header.Value) (bytes : ByteArray) :
    Async (Response Body.Any) := do
  let body ← Body.Full.ofByteArray bytes
  return (Response.new.status status
    |>.header (.mk "content-type") contentType
    |>.header (.mk "x-content-type-options") (.mk "nosniff")
    |>.header (.mk "referrer-policy") (.mk "no-referrer")
    |>.header (.mk "cache-control") (.mk "no-store")).body (Body.Any.ofBody body)

private def cspHeaderValue : Header.Value :=
  (Header.Value.ofString? Html.contentSecurityPolicy).getD (.mk "script-src 'none'")

private def locationHeaderValue (location : String) : Header.Value :=
  (Header.Value.ofString? location).getD (.mk "/")

private def htmlResponse (status : Status) (doc : Html.Document) :
    Async (Response Body.Any) := do
  let body ← Body.Full.ofByteArray doc.render.toUTF8
  return (Response.new.status status
    |>.header (.mk "content-type") (.mk "text/html; charset=utf-8")
    |>.header (.mk "content-security-policy") cspHeaderValue
    |>.header (.mk "x-content-type-options") (.mk "nosniff")
    |>.header (.mk "referrer-policy") (.mk "no-referrer")
    |>.header (.mk "cache-control") (.mk "no-store")).body (Body.Any.ofBody body)

private def redirectResponse (location : String) : Async (Response Body.Any) := do
  let body ← Body.Full.ofByteArray ByteArray.empty
  return (Response.new.status .seeOther
    |>.header (.mk "location") (locationHeaderValue location)
    |>.header (.mk "x-content-type-options") (.mk "nosniff")
    |>.header (.mk "referrer-policy") (.mk "no-referrer")
    |>.header (.mk "cache-control") (.mk "no-store")).body (Body.Any.ofBody body)

private def refused : Async (Response Body.Any) :=
  response .forbidden (.mk "application/json") "{\"ok\":false,\"reason\":\"control request refused\"}".toUTF8

private def controlTimeout : Std.Time.Millisecond.Offset := 10000

private def stopDiagnostic (reason : String) : String :=
  if reason.isEmpty then "stop persistence was not confirmed" else reason

private def controlResponse : ControlResult → ContextAsync (Response Body.Any)
  | .accepted => response .accepted (.mk "application/json") "{\"ok\":true}".toUTF8
  | .clearUnavailable => refused
  | .unavailable | .busy =>
    response .serviceUnavailable (.mk "application/json")
      "{\"ok\":false,\"reason\":\"supervisor unavailable or busy\"}".toUTF8
  | .refused reason =>
    response .serviceUnavailable (.mk "application/json")
      ("{\"ok\":false,\"reason\":" ++ telemetryString (stopDiagnostic reason) ++ "}").toUTF8
  | .unconfirmed reason =>
    response .serviceUnavailable (.mk "application/json")
      ("{\"ok\":false,\"unconfirmed\":true,\"reason\":" ++ telemetryString (stopDiagnostic reason) ++ "}").toUTF8

private def promiseSelector {α : Type} (task : Task (Option α)) : Selector (Option α) where
  tryFn := do
    if ← IO.hasFinished task then
      let value ← (show BaseIO (Option α) from IO.wait task)
      return some value
    else return none
  registerFn waiter := do
    BaseIO.chainTask task fun value =>
      waiter.race (pure ()) (fun promise => promise.resolve (.ok value))
  unregisterFn := pure ()

private def awaitControl (task : Task (Option ControlResult)) : ContextAsync ControlResult := do
  Selectable.one #[
    .case (promiseSelector task) fun outcome =>
      pure (outcome.getD (.unconfirmed "supervisor stopped before confirming stop")),
    .case (← ContextAsync.doneSelector) fun _ =>
      pure (.unconfirmed "viewer shutdown interrupted stop request"),
    .case (← Selector.sleep controlTimeout) fun _ =>
      pure (.unconfirmed "timed out waiting for stop confirmation")
  ]

private def HttpViewer.renderPage (viewer : HttpViewer) (status : Status)
    (query : ViewQuery) (notice : Option ControlNotice) : ContextAsync (Response Body.Any) := do
  let snapshot ← viewer.broadcast.snapshot
  let nowMonoMs ← IO.monoMsNow
  htmlResponse status (renderViewerPage snapshot query viewer.token notice nowMonoMs)

private def HttpViewer.control (viewer : HttpViewer) (request : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let headers := controlHeaders request.line
  if headers.method != "POST" || headers.mediaType != "application/json" ||
      !tokenMatches headers.token viewer.token ||
      headers.length.isNone || headers.length.getD 0 > controlBodyCapacity then
    return ← refused
  let bytes : ByteArray ← request.body.readAll (some controlBodyCapacity.toUInt64)
  let some body := controlBody bytes | return ← refused
  let .ok command := authorizeCommand headers viewer.token body | return ← refused
  match ← viewer.submit command.command with
  | .immediate result => return ← controlResponse result
  | .pending task => return ← controlResponse (← awaitControl task)

private def HttpViewer.controlForm (viewer : HttpViewer) (request : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let headers := formControlHeaders request.line
  if headers.method != "POST" || headers.mediaType != "application/x-www-form-urlencoded" ||
      headers.length.isNone || headers.length.getD 0 > controlBodyCapacity then
    return ← viewer.renderPage .forbidden {} (some .forbidden)
  let bytes : ByteArray ← request.body.readAll (some controlBodyCapacity.toUInt64)
  let some body := controlBody bytes | return ← viewer.renderPage .forbidden {} (some .forbidden)
  let .ok authorized := authorizeFormCommand headers viewer.token body
    | return ← viewer.renderPage .forbidden {} (some .forbidden)
  let payload := authorized.payload
  let query := ViewQuery.ofFormPayload payload true
  let outcome ← match ← viewer.submit payload.command with
    | .immediate result => pure result
    | .pending task => awaitControl task
  match outcome with
  | .accepted => redirectResponse query.href
  | .clearUnavailable => viewer.renderPage .forbidden { query with watch := false } (some .forbidden)
  | .unavailable | .busy =>
    viewer.renderPage .serviceUnavailable { query with watch := false }
      (some (.refused payload.command "supervisor unavailable or busy"))
  | .refused reason =>
    viewer.renderPage .serviceUnavailable { query with watch := false }
      (some (.refused payload.command (stopDiagnostic reason)))
  | .unconfirmed reason =>
    viewer.renderPage .serviceUnavailable { query with watch := false }
      (some (.unconfirmed (stopDiagnostic reason)))

private def bmpMultipartChunk (bytes : ByteArray) : ByteArray :=
  ("--acornframe\r\nContent-Type: image/bmp\r\nContent-Length: " ++
    toString bytes.size ++ "\r\n\r\n").toUTF8 ++ bytes ++ "\r\n".toUTF8

private def drainSubscription (subscription : Subscription) : BaseIO Bool := do
  for _ in [:subscriberCapacity] do
    match ← subscription.poll with
    | .closed => return false
    | .item _ => continue
    | .wait _ => return true
  return true

private def liveStageFrames (broadcast : Broadcast) (subscription : Subscription)
    (stream : Body.Stream) : Async Unit := do
  let sendCurrent : Async Unit := do
    let snapshot ← broadcast.snapshot
    let bmp := StageBmp.render snapshot.world snapshot.observer.latest
    stream.send (.ofByteArray (bmpMultipartChunk bmp))
  sendCurrent
  let pace : Std.Time.Millisecond.Offset :=
    Std.Time.Millisecond.Offset.ofInt (Int.ofNat BrowserConstant.readPace.value)
  EAsync.forIn () fun _ _ => do
    match ← subscription.poll with
    | .closed => return .done ()
    | .item _ =>
      let alive ← drainSubscription subscription
      unless alive do return .done ()
      sendCurrent
      let _ ← Selectable.one #[.case (← Selector.sleep pace) (fun _ => pure ())]
      return .yield ()
    | .wait task =>
      let result ← Selectable.one #[
        .case (promiseSelector task) (fun wake => pure (some wake)),
        .case (← Selector.sleep 2500) (fun _ => pure none)]
      match result with
      | some none => return .done ()
      | some (some ()) =>
        let alive ← drainSubscription subscription
        unless alive do return .done ()
        sendCurrent
        let _ ← Selectable.one #[.case (← Selector.sleep pace) (fun _ => pure ())]
        return .yield ()
      | none =>
        sendCurrent
        return .yield ()

private def HttpViewer.stageStream (viewer : HttpViewer) : ContextAsync (Response Body.Any) := do
  let context ← ContextAsync.getContext
  let some (subscription, _) ← viewer.broadcast.subscribe |
    return ← response .serviceUnavailable (.mk "text/plain") "subscriber capacity reached\n".toUTF8
  let finished ← Std.CancellationToken.new
  let stream ← Body.stream fun stream => do
    try
      liveStageFrames viewer.broadcast subscription stream
    finally
      subscription.close
      finished.cancel
  Async.background do
    let cancelled ← Selectable.one #[
      .case context.doneSelector (fun _ => pure true),
      .case finished.selector (fun _ => pure false)]
    if cancelled then
      subscription.close
      stream.close
  let erased := Body.Any.ofBody stream
  let body := { erased with close := do subscription.close; stream.close; finished.cancel }
  return (Response.new
    |>.header (.mk "content-type") (.mk "multipart/x-mixed-replace; boundary=acornframe")
    |>.header (.mk "x-content-type-options") (.mk "nosniff")
    |>.header (.mk "cache-control") (.mk "no-store")
    |>.header (.mk "x-accel-buffering") (.mk "no")).body body

private def extractRawQuery (uriText : String) : String :=
  match uriText.splitOn "?" with
  | _ :: rest :: _ => (rest.splitOn "#").headD ""
  | _ => ""

private def HttpViewer.request (viewer : HttpViewer) (request : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let path := toString request.line.uri.path
  match path with
  | "/control" => viewer.control request
  | "/control/form" => viewer.controlForm request
  | "/style.css" =>
    response .ok (.mk "text/css; charset=utf-8") viewer.assets.stylesheet.toUTF8
  | "/stage.bmp" =>
    let snapshot ← viewer.broadcast.snapshot
    response .ok (.mk "image/bmp") (StageBmp.render snapshot.world snapshot.observer.latest)
  | "/stream/stage.bmp" => viewer.stageStream
  | "/" | "/index.html" =>
    let query := ViewQuery.parseRaw (extractRawQuery (toString request.line.uri))
    viewer.renderPage .ok query none
  | "/favicon.ico" => response .noContent (.mk "image/x-icon") ByteArray.empty
  | _ => response .notFound (.mk "text/plain; charset=utf-8") "not found\n".toUTF8

def viewerHttpConfig : Http.Config where
  maxConnections := 32
  maxRequests := 1
  maxHeaderBytes := 65536
  lingeringTimeout := 10000
  headerTimeout := 10000
  enableKeepAlive := false
  maximumRecvSize := 2048
  maxBodySize := controlBodyCapacity
  maxChunkSize := controlBodyCapacity
  generateDate := false
  serverName := none

def HttpViewer.serve (viewer : HttpViewer) (port : UInt16) : Async Http.Server :=
  Http.Server.serve (.v4 ⟨Net.IPv4Addr.ofParts 127 0 0 1, port⟩)
    (Http.Server.Handler.ofFns viewer.request (fun _ => pure ()) (fun _ => pure false))
    viewerHttpConfig

end Acorn.Host.Viewer
