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

set_option maxRecDepth 4096 in
private def cspHeaderValue : Header.Value :=
  .mk Html.contentSecurityPolicy (by decide)

private theorem mem_of_getLast?_some : ∀ {l : List Char} {c : Char}, l.getLast? = some c → c ∈ l
  | [], _, h => by cases h
  | [x], c, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self ..
  | _ :: y :: rest, c, h =>
    List.mem_cons_of_mem _ (mem_of_getLast?_some (l := y :: rest) (by simpa using h))

private theorem visibleAscii_validHeaderValue (s : String)
    (hVis : ∀ c ∈ s.toList, '!' ≤ c ∧ c ≤ '~') :
    Header.IsValidHeaderValue s := by
  have hVchar : ∀ c ∈ s.toList, Std.Http.Internal.Char.fieldVchar c = true := by
    intro c hc
    obtain ⟨hLo, hHi⟩ := hVis c hc
    simp [Std.Http.Internal.Char.fieldVchar, Std.Http.Internal.Char.vchar, hLo, hHi]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro c hc
    simp [Std.Http.Internal.Char.fieldContent, hVchar c hc]
  · cases hList : s.toList with
    | nil => rfl
    | cons c cs =>
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      exact hVchar c (hList ▸ List.mem_cons_self ..)
  · cases hLast : s.toList.getLast? with
    | none => rfl
    | some c =>
      simp only [Option.map_some, Option.getD_some]
      exact hVchar c (mem_of_getLast?_some hLast)

private def locationHeaderValue (query : ViewQuery) : Header.Value :=
  .mk query.href (visibleAscii_validHeaderValue query.href (ViewQuery.href_visibleAscii query))

private def htmlResponse (status : Status) (doc : Html.Document) :
    Async (Response Body.Any) := do
  let body ← Body.Full.ofByteArray doc.render.toUTF8
  return (Response.new.status status
    |>.header (.mk "content-type") (.mk "text/html; charset=utf-8")
    |>.header (.mk "content-security-policy") cspHeaderValue
    |>.header (.mk "x-content-type-options") (.mk "nosniff")
    |>.header (.mk "referrer-policy") (.mk "no-referrer")
    |>.header (.mk "cache-control") (.mk "no-store")).body (Body.Any.ofBody body)

private def redirectResponse (query : ViewQuery) : Async (Response Body.Any) := do
  let body ← Body.Full.ofByteArray ByteArray.empty
  return (Response.new.status .seeOther
    |>.header (.mk "location") (locationHeaderValue query)
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
  let query := { ViewQuery.ofPairs payload.pairs with watch := true }
  let outcome ← match ← viewer.submit payload.command with
    | .immediate result => pure result
    | .pending task => awaitControl task
  match outcome with
  | .accepted =>
    let redirectQuery :=
      if payload.command == .clear then
        { query with mode := .live, frame := none, run := none, epoch := none }
      else query
    redirectResponse redirectQuery
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

def paceRemainingMs (lastSent : Option Nat) (nowMs : Nat) (paceMs : Nat) : Nat :=
  match lastSent with
  | none => 0
  | some prev => paceMs - (nowMs - prev)

theorem paceRemainingMs_initial (nowMs paceMs : Nat) :
    paceRemainingMs none nowMs paceMs = 0 := rfl

theorem paceRemainingMs_bounded (lastSent : Option Nat) (nowMs paceMs : Nat) :
    paceRemainingMs lastSent nowMs paceMs ≤ paceMs := by
  cases lastSent with
  | none => exact Nat.zero_le _
  | some prev => exact Nat.sub_le _ _

theorem paceRemainingMs_spacing (prev nowMs paceMs : Nat)
    (hPos : 0 < paceMs) (hZero : paceRemainingMs (some prev) nowMs paceMs = 0) :
    prev + paceMs ≤ nowMs := by
  simp only [paceRemainingMs] at hZero
  omega

private def waitForPace (lastSent : IO.Ref (Option Nat)) (cancel : Std.CancellationToken)
    (paceMs : Nat) : Async Bool :=
  EAsync.forIn false fun _ _ => do
    if ← cancel.isCancelled then return .done false
    let waitMs := paceRemainingMs (← lastSent.get) (← IO.monoMsNow) paceMs
    if waitMs == 0 then return .done true
    let delay : Std.Time.Millisecond.Offset :=
      Std.Time.Millisecond.Offset.ofInt (Int.ofNat waitMs)
    let proceed ← Selectable.one #[
      .case cancel.selector (fun _ => pure false),
      .case (← Selector.sleep delay) (fun _ => pure true)]
    if proceed then return .yield false else return .done false

private def liveStageFrames (subscription : Subscription) (cancel : Std.CancellationToken)
    (stream : Body.Stream) : Async Unit := do
  let lastSent ← IO.mkRef (none : Option Nat)
  let sendCurrent : Async Bool := do
    if !(← waitForPace lastSent cancel BrowserConstant.readPace.value) then
      return false
    let some snapshot ← subscription.snapshot | return false
    let nowMonoMs ← IO.monoMsNow
    let bmp := StageBmp.render (StageBmp.fromSnapshot snapshot nowMonoMs)
    stream.send (.ofByteArray (bmpMultipartChunk bmp))
    lastSent.set (some (← IO.monoMsNow))
    return true
  unless ← sendCurrent do return ()
  EAsync.forIn () fun _ _ => do
    if ← cancel.isCancelled then return .done ()
    match ← subscription.poll with
    | .closed => return .done ()
    | .updated =>
      if ← sendCurrent then return .yield () else return .done ()
    | .wait task =>
      let result ← Selectable.one #[
        .case cancel.selector (fun _ => pure (some none)),
        .case (promiseSelector task) (fun wake => pure (some wake)),
        .case (← Selector.sleep 2500) (fun _ => pure none)]
      match result with
      | some none => return .done ()
      | some (some ()) =>
        if ← sendCurrent then return .yield () else return .done ()
      | none =>
        if ← sendCurrent then return .yield () else return .done ()

private def HttpViewer.stageStream (viewer : HttpViewer) : ContextAsync (Response Body.Any) := do
  let context ← ContextAsync.getContext
  let some subscription ← viewer.broadcast.subscribe |
    return ← response .serviceUnavailable (.mk "text/plain") "subscriber capacity reached\n".toUTF8
  let cancel ← Std.CancellationToken.new
  let finished ← Std.CancellationToken.new
  let stream ← Body.stream fun stream => do
    try
      liveStageFrames subscription cancel stream
    finally
      subscription.close
      finished.cancel
  Async.background do
    let cancelled ← Selectable.one #[
      .case context.doneSelector (fun _ => pure true),
      .case finished.selector (fun _ => pure false)]
    if cancelled then
      cancel.cancel
      subscription.close
      stream.close
  let erased := Body.Any.ofBody stream
  let body := { erased with close := do cancel.cancel; subscription.close; stream.close; finished.cancel }
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
    let nowMonoMs ← IO.monoMsNow
    response .ok (.mk "image/bmp") (StageBmp.render (StageBmp.fromSnapshot snapshot nowMonoMs))
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
