/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Broadcast
import Acorn.Host.Viewer.ControlRequest
import Acorn.Host.Viewer.RunDirectory
import Std.Http.Server

/-!
# Native loopback HTTP transport

The pinned standard HTTP implementation owns sockets, HTTP framing, timeouts
and cancellation. Acorn owns route selection, control admission, bounded
subscriber queues and snapshot/live ordering. A dedicated stream producer
waits outside the broadcast mutex. Closing the response also closes the
subscription, waking an idle producer and releasing its queue.

Static resources are supplied by the native bootstrap; request paths never
select filesystem paths. The listener address is fixed to IPv4 loopback.
-/
namespace Acorn.Host.Viewer
open Std Async Http

/-- The largest RLE/base64 map payload plus bounded JSON metadata. -/
def initialMapCapacity : Nat := 4 * mapSideCapacity * mapSideCapacity + 1024

/-- Initial protocol records precede replay and live records on every subscription. -/
structure InitialFrames where
  /-- Authoritative lifecycle state at subscription registration, when supervised. -/
  control : Option WireText
  /-- Run-owned map snapshot at the same registration boundary. -/
  map : Option (SseLine initialMapCapacity)

/-- The native supervisor's closed command-admission outcomes. -/
inductive ControlResult where
  /-- The command entered the bounded supervisor queue. -/
  | accepted
  /-- No supervisor exists in this configuration. -/
  | unavailable
  /-- The bounded supervisor queue has no free slot. -/
  | busy
  /-- Clear cannot preserve this configuration's file ownership. -/
  | clearUnavailable

/-- Immutable resource bytes loaded by the bootstrap from fixed maintained paths. -/
structure ViewerAssets where
  /-- Main observer page with its token placeholder. -/
  index : String

/-- HTTP capabilities point only to observation and lifecycle owners. -/
structure HttpViewer where
  private mk ::
  private broadcast : Broadcast
  private token : String
  private assets : ViewerAssets
  private initial : ReplaySnapshot → BaseIO InitialFrames
  private submit : Command → BaseIO ControlResult

/-- Startup requires OS entropy; there is no predictable token fallback. -/
def HttpViewer.new (broadcast : Broadcast) (assets : ViewerAssets)
    (initial : ReplaySnapshot → BaseIO InitialFrames) (submit : Command → BaseIO ControlResult) :
    IO HttpViewer := do
  return ⟨broadcast, ← mintControlToken, assets, initial, submit⟩

private def singleHeader (head : Request.Head) (name : Header.Name) : Option String := do
  let values ← head.headers.getAll? name
  if size : values.size = 1 then return (values[0]'(by omega)).value else none

private def controlHeaders (head : Request.Head) : ControlHeaders :=
  let contentType := (singleHeader head (.mk "content-type")).getD ""
  let mediaType := ((contentType.splitOn ";").headD "").trimAscii.toString.toLower
  let length := (singleHeader head (.mk "content-length")).bind fun text =>
    if !text.isEmpty && text.toList.all Char.isDigit then text.toNat? else none
  ⟨toString head.method, mediaType, (singleHeader head (.mk "x-oak-token")).getD "", length⟩

private def response (status : Status) (contentType : Header.Value) (bytes : ByteArray) :
    Async (Response Body.Any) := do
  let body ← Body.Full.ofByteArray bytes
  return (Response.new.status status
    |>.header (.mk "content-type") contentType
    |>.header (.mk "cache-control") (.mk "no-store")).body (Body.Any.ofBody body)

private def refused : Async (Response Body.Any) :=
  response .forbidden (.mk "application/json") "{\"ok\":false,\"reason\":\"control request refused\"}".toUTF8

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
  | .accepted => return ← response .accepted (.mk "application/json") "{\"ok\":true}".toUTF8
  | .clearUnavailable => return ← refused
  | .unavailable | .busy =>
    return ← response .serviceUnavailable (.mk "application/json")
      "{\"ok\":false,\"reason\":\"supervisor unavailable or busy\"}".toUTF8

private def sendLine (stream : Body.Stream) (text : String) : Async Unit :=
  stream.send (.ofByteArray ("data: " ++ text ++ "\n\n").toUTF8)

private def wakeSelector (task : Task (Option Unit)) : Selector (Option Unit) where
  tryFn := do
    if ← IO.hasFinished task then
      let value ← (show BaseIO (Option Unit) from IO.wait task)
      return some value
    else return none
  registerFn waiter := do
    BaseIO.chainTask task fun value =>
      waiter.race (pure ()) (fun promise => promise.resolve (.ok value))
  unregisterFn := pure ()

private def liveFrames (subscription : Subscription) (stream : Body.Stream) : Async Unit := do
  repeat
    match ← subscription.poll with
    | .closed => return
    | .item text => sendLine stream text.val
    | .wait task =>
      let result ← Selectable.one #[
        .case (wakeSelector task) (fun wake => pure (some wake)),
        .case (← Selector.sleep 5000) (fun _ => pure none)]
      match result with
      | some none => return
      | some (some ()) => pure ()
      | none => stream.send (.ofByteArray ": keepalive\n\n".toUTF8)

private def HttpViewer.events (viewer : HttpViewer) : ContextAsync (Response Body.Any) := do
  let context ← ContextAsync.getContext
  let some (subscription, snapshot) ← viewer.broadcast.subscribe |
    return ← response .serviceUnavailable (.mk "text/plain") "subscriber capacity reached\n".toUTF8
  let finished ← Std.CancellationToken.new
  let initial ← viewer.initial snapshot
  let stream ← Body.stream fun stream => do
    try
      if let some control := initial.control then sendLine stream control.val
      if let some map := initial.map then sendLine stream map.val
      for frame in snapshot.frames.values do sendLine stream frame.val
      liveFrames subscription stream
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
    |>.header (.mk "content-type") (.mk "text/event-stream")
    |>.header (.mk "cache-control") (.mk "no-cache")
    |>.header (.mk "access-control-allow-origin") (.mk "*")
    |>.header (.mk "x-accel-buffering") (.mk "no")).body body

private def HttpViewer.request (viewer : HttpViewer) (request : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let path := toString request.line.uri.path
  match path with
  | "/control" => viewer.control request
  | "/events" => viewer.events
  | "/" | "/index.html" =>
    response .ok (.mk "text/html; charset=utf-8")
      (viewer.assets.index.replace "__OAK_CONTROL_TOKEN__" viewer.token).toUTF8
  | "/favicon.ico" => response .noContent (.mk "image/x-icon") ByteArray.empty
  | _ => response .notFound (.mk "text/plain; charset=utf-8") "not found\n".toUTF8

/-- Bounds cover both subscriber and ordinary HTTP connections; request bodies never exceed control capacity. -/
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

/-- Bind only loopback and use the actual route/admission implementation with pinned transport bounds. -/
def HttpViewer.serve (viewer : HttpViewer) (port : UInt16) : Async Http.Server :=
  Http.Server.serve (.v4 ⟨Net.IPv4Addr.ofParts 127 0 0 1, port⟩)
    (Http.Server.Handler.ofFns viewer.request (fun _ => pure ()) (fun _ => pure false))
    viewerHttpConfig

end Acorn.Host.Viewer
