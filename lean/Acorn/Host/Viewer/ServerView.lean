import Acorn.Host.Viewer.Html
import Acorn.Host.Viewer.Broadcast
import Acorn.Host.Viewer.BrowserKernel
import Acorn.Host.Viewer.ControlRequest
import Acorn.Host.Viewer.DecimalText

namespace Acorn.Host.Viewer

open Html DecimalText

inductive ViewMode where
  | live
  | paused
  deriving DecidableEq, BEq

inductive RefreshMode where
  | auto
  | sec1
  | sec2
  | sec5
  | off
  deriving DecidableEq, BEq

def RefreshMode.tag : RefreshMode → String
  | .auto => "auto"
  | .sec1 => "1"
  | .sec2 => "2"
  | .sec5 => "5"
  | .off => "off"

def RefreshMode.parse : String → RefreshMode
  | "1" => .sec1
  | "2" => .sec2
  | "5" => .sec5
  | "off" => .off
  | _ => .auto

structure ViewQuery where
  mode : ViewMode := .live
  frame : Option Nat := none
  refresh : RefreshMode := .auto
  inside : Bool := false
  stream : Bool := false
  watch : Bool := false
  deriving DecidableEq, BEq

def ViewQuery.ofPairs (pairs : List (String × String)) : ViewQuery :=
  let stream := formLookup pairs "stream" == some "1"
  let mode :=
    if stream then ViewMode.live
    else match formLookup pairs "view" with
      | some "paused" => ViewMode.paused
      | _ => ViewMode.live
  let frame := if mode == .paused then (formLookup pairs "frame").bind Digits.read else none
  let refresh := match formLookup pairs "refresh" with
    | some raw => RefreshMode.parse raw
    | none => .auto
  let inside := formLookup pairs "inside" == some "1"
  let watch := formLookup pairs "watch" == some "1"
  { mode, frame, refresh, inside, stream, watch }

def ViewQuery.parseRaw (rawQuery : String) : ViewQuery :=
  let trimmed := if rawQuery.startsWith "?" then (rawQuery.drop 1).toString else rawQuery
  match parseFormPairs trimmed with
  | some pairs => ViewQuery.ofPairs pairs
  | none => {}

def ViewQuery.href (q : ViewQuery) : String :=
  let parts : List String :=
    (if q.mode == .paused then ["view=paused"] else []) ++
    (match q.frame with | some n => [s!"frame={n}"] | none => []) ++
    (if q.refresh != .auto then [s!"refresh={q.refresh.tag}"] else []) ++
    (if q.inside then ["inside=1"] else []) ++
    (if q.stream then ["stream=1"] else []) ++
    (if q.watch then ["watch=1"] else [])
  if parts.isEmpty then "/" else "/?" ++ String.intercalate "&" parts

structure DisplayProjection where
  clampedIdx : Option Nat
  displaySummary : Option FrameSummary
  selectedFull : Option ServerFrame
  trailSummaries : List FrameSummary
  selectedIsEarlier : Bool

def projectDisplay (summaries : List FrameSummary) (latest : Option ServerFrame)
    (query : ViewQuery) : DisplayProjection :=
  let bufferedCount := summaries.length
  if bufferedCount == 0 then
    { clampedIdx := none
      displaySummary := latest.map (·.summary)
      selectedFull := latest
      trailSummaries := []
      selectedIsEarlier := false }
  else
    let idx := match query.mode, query.frame with
      | .paused, some req => max 1 (min bufferedCount req) - 1
      | _, _ => bufferedCount - 1
    let sel := summaries[idx]?
    let displaySummary := sel.or (latest.map (·.summary))
    let selectedIsEarlier := query.mode == .paused && idx + 1 < bufferedCount
    let selectedFull :=
      if selectedIsEarlier then none
      else match latest, sel with
        | some f, some s =>
          if f.summary.lifetimeStep == s.lifetimeStep &&
              f.summary.worldStep == s.worldStep &&
              f.summary.terminal == s.terminal then some f
          else none
        | _, _ => none
    { clampedIdx := some idx
      displaySummary
      selectedFull
      trailSummaries := summaries.take (idx + 1)
      selectedIsEarlier }

theorem projectDisplay_paused_earlier (summaries : List FrameSummary)
    (latest : Option ServerFrame) (query : ViewQuery) (req : Nat)
    (hMode : query.mode = .paused) (hFrame : query.frame = some req)
    (hNonEmpty : 0 < summaries.length)
    (hEarlier : max 1 (min summaries.length req) < summaries.length) :
    let proj := projectDisplay summaries latest query
    proj.selectedFull = none ∧ proj.selectedIsEarlier = true ∧
      proj.trailSummaries = summaries.take (max 1 (min summaries.length req)) := by
  have hNeZero : (summaries.length == 0) = false := beq_false_of_ne (Nat.ne_of_gt hNonEmpty)
  have hPos : 1 ≤ max 1 (min summaries.length req) := Nat.le_max_left _ _
  have hSubAdd : max 1 (min summaries.length req) - 1 + 1 = max 1 (min summaries.length req) := by
    omega
  have hPaused : (ViewMode.paused == ViewMode.paused) = true := rfl
  simp [projectDisplay, hNeZero, hMode, hFrame, hSubAdd, hPaused, hEarlier]

inductive ControlNotice where
  | forbidden
  | refused (command : Command) (reason : String)
  | unconfirmed (reason : String)

def viewerStylesheet : String :=
  ":root{--bg:#080b10;--panel:#11161d;--panel2:#161c25;--border:#242c38;" ++
  "--ink:#e6edf3;--dim:#8b97a6;--faint:#7d8997;" ++
  "--accent:#7ee787;--accent2:#79c0ff;--warn:#f0883e;--bad:#ff7b72;" ++
  "--gold:#ffd24a;--violet:#bc8cff;--opt1:#7ee787;--opt2:#e3b341;--opt3:#c75d2c;}\n" ++
  "*{box-sizing:border-box;}html,body{min-height:100%;}\n" ++
  "body{margin:0;background:var(--bg);color:var(--ink);" ++
  "font:12px/1.45 ui-monospace,'SF Mono',Menlo,Consolas,monospace;-webkit-font-smoothing:antialiased;}\n" ++
  "h1,h2,h3{margin:0;font-weight:600;}sub,sup{font-size:max(.9em,10px);}\n" ++
  ".panel h3{font-size:10px;color:var(--dim);text-transform:uppercase;letter-spacing:.8px;margin:8px 0 3px;}\n" ++
  "a{color:var(--accent2);text-decoration:none;}a:hover{text-decoration:underline;}\n" ++
  "#top{display:flex;gap:8px;align-items:center;flex-wrap:wrap;padding:7px 10px;" ++
  "background:linear-gradient(180deg,#141a23,#0e131a);border-bottom:1px solid var(--border);position:sticky;top:0;z-index:20;}\n" ++
  "#top h1{font-size:15px;color:var(--accent);letter-spacing:1.5px;margin-right:4px;}\n" ++
  "#top .sub{color:var(--faint);font-size:11px;letter-spacing:.5px;}\n" ++
  ".stat{display:flex;flex-direction:column;align-items:flex-start;}\n" ++
  ".stat .k{color:var(--faint);font-size:10px;text-transform:uppercase;letter-spacing:.5px;}\n" ++
  ".stat .v{color:var(--ink);font-variant-numeric:tabular-nums;}\n" ++
  "#topright{display:flex;gap:8px;align-items:center;flex-wrap:wrap;justify-content:flex-end;margin-left:auto;max-width:100%;min-width:0;}\n" ++
  "#topright>*{min-width:0;max-width:100%;}\n" ++
  "#streamhealth{display:flex;flex-wrap:wrap;gap:4px;min-width:0;max-width:44ch;overflow-wrap:anywhere;}\n" ++
  "#runctl{display:flex;gap:6px;align-items:center;flex-wrap:wrap;}\n" ++
  ".ctl-form{display:inline-flex;margin:0;}\n" ++
  ".ctl{font:inherit;font-size:11px;letter-spacing:.4px;padding:3px 11px;border-radius:99px;" ++
  "border:1px solid var(--border);background:#1a212b;color:var(--ink);cursor:pointer;}\n" ++
  ".ctl:hover:not(:disabled){border-color:var(--accent);color:var(--accent);}\n" ++
  ".ctl:disabled{opacity:.4;cursor:not-allowed;}\n" ++
  ".ctl.danger:hover:not(:disabled){border-color:var(--warn);color:var(--warn);}\n" ++
  ".runstate{font-size:11px;color:var(--faint);letter-spacing:.4px;}\n" ++
  ".runstate.on{color:var(--accent);}.runstate.busy{color:var(--gold);}.runstate.off{color:var(--warn);}\n" ++
  "#conn{overflow-wrap:anywhere;white-space:normal;padding:2px 9px;border-radius:99px;border:1px solid var(--border);font-size:11px;letter-spacing:.5px;}\n" ++
  "#conn.live{color:var(--accent);border-color:#28502f;background:#0f2114;}\n" ++
  "#conn.wait{color:var(--warn);border-color:#4a3417;background:#20170c;}\n" ++
  "#conn.dead{color:var(--bad);border-color:#5a2a28;background:#231212;}\n" ++
  ".pill{padding:2px 9px;border-radius:99px;border:1px solid var(--border);font-size:11px;letter-spacing:.3px;}\n" ++
  ".pill.reset{color:var(--bad);border-color:#5a2a28;background:#231212;}\n" ++
  ".pill.live{color:var(--accent);border-color:#28502f;background:#0f2114;}\n" ++
  ".pill.fresh{color:var(--dim);border-color:#2d3744;background:#0d1218;}\n" ++
  ".pill.unknown{color:var(--faint);border-color:#242c38;background:#0a0e14;}\n" ++
  ".pill.resumed{color:var(--accent2);border-color:#1c3a5a;background:#0d1b2a;}\n" ++
  ".pill.cleared{color:var(--gold);border-color:#594a17;background:#211b0b;}\n" ++
  ".broken{color:var(--bad)!important;font-weight:700;}\n" ++
  ".notice-banner{margin:10px 10px 0;padding:10px 12px;border-radius:8px;border:1px solid #5a2a28;" ++
  "background:#231212;color:var(--bad);display:flex;gap:12px;align-items:center;justify-content:space-between;flex-wrap:wrap;}\n" ++
  ".diag-banner{margin:10px 10px 0;padding:9px 12px;border-radius:8px;border:1px solid #4a3417;" ++
  "background:#17130c;color:var(--warn);display:flex;flex-direction:column;gap:5px;}\n" ++
  ".diag-banner.fault{border-color:#5a2a28;background:#231212;color:var(--bad);}\n" ++
  ".diag-banner .diag-head{font-weight:600;overflow-wrap:anywhere;}\n" ++
  ".diag-banner .diag-warn{color:var(--bad);font-weight:600;overflow-wrap:anywhere;}\n" ++
  ".stage-caption{padding:6px 12px;border-top:1px solid var(--border);background:#0d1218;color:var(--dim);font-size:10.5px;display:flex;gap:12px;flex-wrap:wrap;justify-content:space-between;}\n" ++
  ".scope-note{color:var(--faint);font-size:10px;margin:0 0 6px;line-height:1.4;}\n" ++
  "#welcome{display:flex;gap:24px;align-items:center;justify-content:space-between;padding:14px 20px 6px;}\n" ++
  "#welcome>*{min-width:0;}#welcome h2{font-size:21px;color:var(--ink);letter-spacing:-.5px;}\n" ++
  "#welcome p{margin:5px 0;color:var(--dim);max-width:80ch;}#welcome>p{max-width:34ch;flex-shrink:0;}\n" ++
  "#welcome a{display:block;margin-top:7px;}\n" ++
  ".goal-summary .q{font-size:18px;margin-bottom:8px;}\n" ++
  ".research-details{margin:0 10px 14px;border:1px solid var(--border);border-radius:9px;background:var(--bg);}\n" ++
  ".research-details>summary{padding:14px;color:var(--accent2);cursor:pointer;font-size:13px;}\n" ++
  ".research-details>summary:hover{color:var(--ink);}\n" ++
  "#mission{display:grid;grid-template-columns:minmax(300px,1.3fr) minmax(540px,2fr) minmax(290px,1fr);gap:10px;padding:10px 10px 0;align-items:stretch;}\n" ++
  "#main{display:grid;grid-template-columns:minmax(680px,1fr) 366px;gap:10px;padding:10px;align-items:start;}\n" ++
  "#left{display:flex;flex-direction:column;gap:10px;min-width:0;}\n" ++
  "#right{display:flex;flex-direction:column;gap:10px;min-width:0;}\n" ++
  "#world-panels{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px;padding:0 10px 10px;}\n" ++
  "#world-panels>.panel{display:grid;grid-template-columns:minmax(0,1fr) 204px;column-gap:16px;align-content:start;}\n" ++
  "#world-panels>.panel>.world-svg{grid-column:2;grid-row:1 / span 20;width:200px;height:200px;}\n" ++
  "#world-panels>.panel>:not(.world-svg){grid-column:1;}\n" ++
  "#bottom{display:grid;grid-template-columns:minmax(430px,1.35fr) minmax(330px,1fr) minmax(300px,.95fr);gap:10px;padding:10px 10px 14px;align-items:start;}\n" ++
  "#col3{display:flex;flex-direction:column;gap:10px;min-width:0;}\n" ++
  ".panel{background:var(--panel);border:1px solid var(--border);border-radius:9px;padding:10px 11px;min-width:0;}\n" ++
  ".panel>h2{font-size:10.5px;color:var(--accent2);text-transform:uppercase;letter-spacing:1.3px;margin-bottom:2px;}\n" ++
  ".panel>.lede,.panel .lede{color:var(--dim);font-size:11px;margin-bottom:8px;line-height:1.45;}\n" ++
  "details.cite{margin:-3px 0 8px;}details.cite summary{color:var(--faint);font-size:10px;cursor:pointer;letter-spacing:.3px;}\n" ++
  "details.cite summary:hover{color:var(--dim);}\n" ++
  "details.cite .body{color:var(--faint);font-size:10px;line-height:1.45;margin-top:4px;padding-left:8px;border-left:2px solid #2d3744;}\n" ++
  "svg.block,img.stage-img{display:block;width:100%;height:auto;background:#080b10;border:1px solid var(--border);border-radius:6px;}\n" ++
  "img.stage-img{image-rendering:pixelated;border:0;border-radius:0;}\n" ++
  "#stage{position:relative;border-radius:10px;overflow:hidden;border:1px solid var(--border);background:#0a0e14;}\n" ++
  "#map-surface{position:relative;background:#0a0e14;}\n" ++
  "#map-surface svg.stage-svg{display:block;width:100%;height:auto;}\n" ++
  ".empty-stage{min-height:280px;padding:28px 24px;display:flex;flex-direction:column;justify-content:center;align-items:center;text-align:center;gap:10px;background:#0a0e14;}\n" ++
  ".empty-stage h3{font-size:15px;color:var(--ink);text-transform:none;letter-spacing:0;}\n" ++
  ".empty-stage p{margin:0;color:var(--dim);max-width:62ch;}\n" ++
  ".tail{width:100%;max-width:72ch;text-align:left;background:#080b10;border:1px solid var(--border);border-radius:6px;padding:8px 10px;color:var(--warn);font-size:11px;overflow:auto;margin:4px 0 0;}\n" ++
  ".hudrow{display:flex;gap:12px;justify-content:space-between;flex-wrap:wrap;line-height:1.45;padding:8px 12px;background:var(--panel);}\n" ++
  ".hudbox{min-width:0;overflow-wrap:anywhere;}#hud-foot{border-top:1px solid var(--border);}#hud-head{border-bottom:1px solid var(--border);}\n" ++
  "#hud-goal{flex:1 1 280px;}#hud-goal .lbl{color:var(--faint);font-size:10px;text-transform:uppercase;letter-spacing:1px;}\n" ++
  "#hud-goal .txt{color:var(--gold);font-size:14px;font-weight:600;}#hud-goal .meta{color:var(--dim);font-size:10.5px;}\n" ++
  "#hud-time{margin-left:auto;text-align:right;}#hud-time .t{font-size:15px;font-variant-numeric:tabular-nums;}\n" ++
  "#hud-time .lbl{color:var(--faint);font-size:10px;text-transform:uppercase;letter-spacing:1px;}\n" ++
  "#hud-time .hint{color:var(--dim);font-size:10.5px;}\n" ++
  "#hud-vitals{display:flex;flex-wrap:wrap;gap:8px;align-items:center;}\n" ++
  "#hud-skill{margin-left:auto;text-align:right;}#hud-skill .lbl{color:var(--faint);font-size:10px;text-transform:uppercase;letter-spacing:1px;}\n" ++
  "#hud-skill .v{font-size:14px;font-weight:700;}#hud-skill .sub2{color:var(--dim);font-size:10px;}\n" ++
  "#hud-skill .v.none{color:var(--faint);}#hud-skill .v.opt1{color:var(--opt1);}#hud-skill .v.opt2{color:var(--opt2);}#hud-skill .v.opt3{color:var(--opt3);}\n" ++
  "progress.energy-bar{width:104px;height:10px;accent-color:var(--accent);}\n" ++
  ".inv{display:flex;gap:9px;font-size:12.5px;font-variant-numeric:tabular-nums;flex-wrap:wrap;}\n" ++
  ".inv .off{opacity:.35;}\n" ++
  "#transport{display:flex;gap:7px;align-items:center;flex-wrap:wrap;}\n" ++
  ".btn{display:inline-block;background:#1a212b;color:var(--ink);border:1px solid var(--border);border-radius:6px;padding:4px 9px;font:inherit;font-size:11px;cursor:pointer;text-decoration:none;}\n" ++
  ".btn:hover{border-color:var(--accent2);color:#fff;text-decoration:none;}\n" ++
  ".btn.active{background:#12314f;border-color:var(--accent2);color:#cfe8ff;}\n" ++
  ".btn.livebtn.active{background:#123021;border-color:var(--accent);color:#b7f0c4;}\n" ++
  ".jump-form{display:inline-flex;gap:4px;align-items:center;margin:0;}\n" ++
  ".jump-input{width:70px;background:#0d1218;color:var(--ink);border:1px solid var(--border);border-radius:6px;padding:3px 6px;font:inherit;font-size:11px;}\n" ++
  ".lag{font-size:10.5px;color:var(--warn);}.lag.ok{color:var(--faint);}\n" ++
  ".thesis .q{color:var(--ink);font-size:20px;line-height:1.25;font-weight:650;letter-spacing:-.3px;margin:0 0 10px;}\n" ++
  ".thesis p{margin:0 0 4px;color:var(--dim);font-size:11px;line-height:1.5;}.thesis p.fine{color:var(--faint);font-size:10px;}\n" ++
  "#loop{display:grid;grid-template-columns:repeat(5,minmax(0,1fr));gap:8px;margin-top:6px;}\n" ++
  ".node{position:relative;background:#0d1218;border:1px solid var(--border);border-radius:7px;padding:7px 9px 6px;min-width:0;}\n" ++
  ".node .t{font-size:10px;text-transform:uppercase;letter-spacing:1px;color:var(--accent2);}\n" ++
  ".node .v{font-size:12px;font-weight:600;margin:3px 0 1px;font-variant-numeric:tabular-nums;overflow-wrap:anywhere;}\n" ++
  ".node .c{font-size:10px;color:var(--faint);line-height:1.35;}\n" ++
  ".node.on{border-color:#2f6b3a;box-shadow:inset 0 0 0 1px rgba(126,231,135,.45);}\n" ++
  ".node.on .t{color:var(--accent);}.node.on .t::after{content:' · now';letter-spacing:0;text-transform:none;}\n" ++
  ".tiles{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:8px;margin-top:6px;}\n" ++
  ".tile{background:#0d1218;border:1px solid var(--border);border-radius:7px;padding:7px 9px 6px;min-width:0;}\n" ++
  ".tile .k{font-size:10px;text-transform:uppercase;letter-spacing:1px;color:var(--faint);}\n" ++
  ".tile .v{font-size:17px;font-weight:700;margin:2px 0 0;font-variant-numeric:tabular-nums;line-height:1.2;}\n" ++
  ".tile .d{font-size:10px;color:var(--dim);line-height:1.35;}\n" ++
  ".up{color:var(--accent);}.down{color:var(--bad);}.flat{color:var(--dim);}\n" ++
  ".kv{display:flex;justify-content:space-between;gap:8px;padding:2px 0;font-size:11.5px;}\n" ++
  ".kv span{color:var(--dim);}.kv b{font-weight:600;font-variant-numeric:tabular-nums;text-align:right;overflow-wrap:anywhere;}\n" ++
  ".legend-row{display:flex;gap:14px;margin-top:6px;flex-wrap:wrap;}\n" ++
  ".legend{font-size:10px;color:var(--faint);line-height:1.5;}\n" ++
  ".swatch{display:inline-block;width:8px;height:8px;border-radius:2px;vertical-align:middle;margin-right:4px;}\n" ++
  ".sw-opt1{background:var(--opt1);}.sw-opt2{background:var(--opt2);}.sw-opt3{background:var(--opt3);}.sw-goal{background:var(--violet);}\n" ++
  ".sw-dem{background:var(--accent2);}.sw-ctl{background:var(--accent);}.sw-met{background:var(--gold);}.sw-opt{background:var(--warn);}\n" ++
  ".sw-w0{background:#3a6ea5;}.sw-w1{background:#d9c58b;}.sw-w2{background:#7da05e;}.sw-w3{background:#5c8a3f;}\n" ++
  ".sw-w4{background:#2e6b2f;}.sw-w5{background:#8a8a8a;}.sw-w6{background:#b0b0b0;}.sw-w7{background:#d4a017;}\n" ++
  "#goals{display:flex;flex-direction:column;gap:1px;margin:4px -4px 0;padding:0 4px;}\n" ++
  ".goal{display:flex;gap:7px;align-items:center;font-size:11px;padding:2.5px 5px;border-radius:4px;}\n" ++
  ".goal.cur{background:#132030;box-shadow:inset 2px 0 0 var(--accent2);}\n" ++
  ".goal .st{width:9px;height:9px;border-radius:2px;flex:none;}\n" ++
  ".st.ok{background:#3fb950;}.st.no{background:var(--bad);}.st.wait{background:#242c38;}.st.run{background:var(--gold);}\n" ++
  ".goal .nm{flex:1;min-width:0;overflow-wrap:anywhere;}.goal .at{max-width:50%;color:var(--faint);font-size:10px;text-align:right;}\n" ++
  ".goal.cur .nm{color:#fff;}\n" ++
  ".agreement-primary{margin:10px 0 12px;padding:10px 12px;border:1px solid #344253;border-radius:8px;background:rgba(126,231,135,.04);}\n" ++
  ".agreement-primary strong{display:block;font-size:28px;color:var(--ink);line-height:1.4;}\n" ++
  ".agreement-primary progress{display:block;width:100%;height:10px;accent-color:#7ee787;margin:6px 0;}\n" ++
  ".goal-primary strong{font-size:36px;}\n" ++
  ".agreement-channels{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:8px;margin:10px 0;}\n" ++
  ".agreement-card{min-width:0;border:1px solid #344253;border-radius:6px;padding:8px 10px;overflow-wrap:anywhere;background:#0d1218;}\n" ++
  ".agreement-card h3{font-size:11.5px;margin:0 0 4px;text-transform:none;color:var(--ink);}\n" ++
  ".agreement-card strong{font-size:16px;color:var(--ink);}\n" ++
  ".agreement-primary strong.has-score,.agreement-card strong.has-score{color:#7ee787;}\n" ++
  ".agreement-card p{font-size:10.5px;color:#a9b4c0;line-height:1.45;margin:4px 0 0;}\n" ++
  ".learner-detail{margin-top:5px;border-top:1px solid #202834;padding-top:4px;}\n" ++
  ".learner-detail summary{color:var(--dim);cursor:pointer;font-size:10px;}\n" ++
  ".learner-detail pre{color:var(--faint);font-size:10px;line-height:1.5;max-height:120px;overflow:auto;margin:4px 0 1px;white-space:pre-wrap;}\n" ++
  "table.data{width:100%;border-collapse:collapse;font-size:10.5px;margin-top:6px;}\n" ++
  "table.data th,table.data td{text-align:left;padding:3px 5px;border-bottom:1px solid #202834;font-variant-numeric:tabular-nums;}\n" ++
  "table.data th{color:var(--faint);font-weight:600;text-transform:uppercase;font-size:9.5px;}\n" ++
  "@media(max-width:1280px){#main{grid-template-columns:minmax(580px,1fr) 320px;}#bottom{grid-template-columns:minmax(360px,1.25fr) minmax(280px,1fr) minmax(260px,.9fr);}#mission{grid-template-columns:minmax(280px,1.25fr) minmax(420px,1.9fr) minmax(240px,1fr);}}\n" ++
  "@media(max-width:1100px){#world-panels{grid-template-columns:1fr;}}\n" ++
  "@media(max-width:1040px){body{overflow-x:hidden;}#mission{grid-template-columns:1fr;}#main{grid-template-columns:1fr;}#bottom{grid-template-columns:1fr;}.tiles{grid-template-columns:repeat(4,minmax(0,1fr));}#evidence-mode::after{content:' · COMPACT';}}\n" ++
  "@media(max-width:700px){#welcome{display:block;padding:12px 10px 2px;}#welcome>p{max-width:none;}#loop{grid-template-columns:1fr 1fr;}.tiles{grid-template-columns:repeat(2,minmax(0,1fr));}}\n" ++
  "@media(max-width:600px){.agreement-channels{grid-template-columns:minmax(0,1fr);}}\n" ++
  "@media(max-width:500px){#world-panels>.panel{display:block;}#world-panels>.panel>.world-svg{margin:10px auto;}}\n"

private def terrainHex : Nat → String
  | 0 => "#3a6ea5"
  | 1 => "#d9c58b"
  | 2 => "#7da05e"
  | 3 => "#5c8a3f"
  | 4 => "#2e6b2f"
  | 5 => "#8a8a8a"
  | 6 => "#b0b0b0"
  | 7 => "#d4a017"
  | _ => "#0a0e14"

private def optionColor : Nat → String
  | 0 => "#7ee787"
  | 1 => "#e3b341"
  | 2 => "#c75d2c"
  | _ => "#484f58"

private def optionClass : Nat → String
  | 0 => "v opt1"
  | 1 => "v opt2"
  | 2 => "v opt3"
  | _ => "v none"

private def dayPhaseLabel : Nat → String
  | 0 => "dawn"
  | 1 => "morning"
  | 2 => "noon"
  | 3 => "afternoon"
  | 4 => "dusk"
  | 5 => "evening"
  | 6 => "midnight"
  | _ => "pre-dawn"

private def facingArrowPoints (cx cy : Int) (facing : Nat) : String :=
  match facing with
  | 0 => s!"{cx},{cy - 5} {cx - 4},{cy + 4} {cx + 4},{cy + 4}"
  | 1 => s!"{cx},{cy + 5} {cx - 4},{cy - 4} {cx + 4},{cy - 4}"
  | 2 => s!"{cx + 5},{cy} {cx - 4},{cy - 4} {cx - 4},{cy + 4}"
  | _ => s!"{cx - 5},{cy} {cx + 4},{cy - 4} {cx + 4},{cy + 4}"

private def hiddenViewInputs (q : ViewQuery) : List Node :=
  (if q.mode == .paused then [vd .input [kv .type "hidden", kv .name "view", kv .value "paused"]] else []) ++
  (match q.frame with
    | some n => [vd .input [kv .type "hidden", kv .name "frame", kv .value (toString n)]]
    | none => []) ++
  (if q.refresh != .auto then [vd .input [kv .type "hidden", kv .name "refresh", kv .value q.refresh.tag]] else []) ++
  (if q.inside then [vd .input [kv .type "hidden", kv .name "inside", kv .value "1"]] else []) ++
  (if q.stream then [vd .input [kv .type "hidden", kv .name "stream", kv .value "1"]] else [])

def effectiveRefreshSeconds (phase : Phase) (q : ViewQuery) : Option Nat :=
  match q.refresh with
  | .off => none
  | .sec1 => some 1
  | .sec2 => some 2
  | .sec5 => some 5
  | .auto =>
    if q.watch then some 1
    else
      match phase with
      | .starting _ | .stopping _ | .archiving => some 1
      | .running _ =>
        if q.stream then some 5
        else if q.mode == .live then some 2
        else none
      | .idle => none

theorem effectiveRefreshSeconds_stream_running (gen : UInt64) (q : ViewQuery)
    (hRefresh : q.refresh = .auto) (hStream : q.stream = true) (hWatch : q.watch = false) :
    effectiveRefreshSeconds (.running gen) q = some 5 := by
  simp [effectiveRefreshSeconds, hRefresh, hStream, hWatch]

private def formatPermilleScore (score : Option Nat) (scale : Nat) : String :=
  match score with
  | none => "—"
  | some s =>
    if scale == 1000 then formatDecimal1 s ++ "%"
    else if scale == 0 then toString s
    else formatDecimal1 (s * 1000 / scale) ++ "%"

private def kvRow (label value : String) (broken : Bool := false) : Node :=
  el .div [kv .cls "kv"] [
    el .span [] [txt label],
    el .b (if broken then [kv .cls "broken"] else []) [txt value]
  ]

private def renderStageSvg (world : Option ((key : MapKey) × WorldMemory key))
    (selectedFull : Option ServerFrame) (summary : FrameSummary)
    (trailSummaries : List FrameSummary) : Node := Id.run do
  let cols : Nat := 96
  let rows : Nat := 54
  let tilePx : Nat := 12
  let svgW := cols * tilePx
  let svgH := rows * tilePx
  let halfW : Int := (cols / 2 : Nat)
  let halfH : Int := (rows / 2 : Nat)
  let cx := summary.x
  let cy := summary.y
  let side : Int := summary.side
  let mut terrainNodes : Array Node := #[]
  for ry in [:rows] do
    let wy := cy - halfH + (ry : Int)
    let mut runStart : Nat := 0
    let mut runKind : Option Nat := none
    for rx in [:cols] do
      let wx := cx - halfW + (rx : Int)
      let cellKind : Option Nat :=
        if 0 ≤ wx && wx < side && 0 ≤ wy && wy < side then
          let sensorKind : Option Nat :=
            match selectedFull with
            | some f =>
              let dx := wx - f.summary.x
              let dy := wy - f.summary.y
              if -5 ≤ dx && dx ≤ 5 && -5 ≤ dy && dy ≤ 5 then
                let idx := (dy + 5).toNat * 11 + (dx + 5).toNat
                f.tiles[idx]?
              else none
            | none => none
          match sensorKind with
          | some k => some k
          | none =>
            match world with
            | some ⟨key, mem⟩ =>
              match mapIndex key.side wx wy with
              | some mapIdx =>
                let byte := mem.observations.bytes[mapIdx.val]'(by
                  rw [mem.observations.size]; exact mapIdx.isLt)
                if byte == 255 then none else some byte.toNat
              | none => none
            | none => none
        else none
      if cellKind != runKind then
        if let some k := runKind then
          let runLen := rx - runStart
          terrainNodes := terrainNodes.push (el .rect [
            kv .x (toString (runStart * tilePx)),
            kv .y (toString (ry * tilePx)),
            kv .width (toString (runLen * tilePx)),
            kv .height (toString tilePx),
            kv .fill (terrainHex k)
          ] [])
        runStart := rx
        runKind := cellKind
    if let some k := runKind then
      let runLen := cols - runStart
      terrainNodes := terrainNodes.push (el .rect [
        kv .x (toString (runStart * tilePx)),
        kv .y (toString (ry * tilePx)),
        kv .width (toString (runLen * tilePx)),
        kv .height (toString tilePx),
        kv .fill (terrainHex k)
      ] [])
  let mut overlayNodes : Array Node := #[]
  let phase := if summary.dayLength > 0 then
    BrowserNat.dayPhase.eval (BrowserNat.dayArguments summary.worldStep summary.dayLength)
    else 0
  if phase ≥ 4 then
    let nightOp := if phase == 4 || phase == 7 then "0.22" else "0.38"
    overlayNodes := overlayNodes.push (el .rect [
      kv .x "0", kv .y "0", kv .width (toString svgW), kv .height (toString svgH),
      kv .fill "#081230", kv .fillOpacity nightOp
    ] [])
  let trailPoints := (trailSummaries.drop (trailSummaries.length - 80)).filterMap fun s =>
    let rx := s.x - (cx - halfW)
    let ry := s.y - (cy - halfH)
    if 0 ≤ rx && rx < cols && 0 ≤ ry && ry < rows then
      some s!"{rx.toNat * tilePx + tilePx / 2},{ry.toNat * tilePx + tilePx / 2}"
    else none
  if trailPoints.length ≥ 2 then
    overlayNodes := overlayNodes.push (el .polyline [
      kv .points (String.intercalate " " trailPoints),
      kv .fill "none", kv .stroke "#79c0ff", kv .strokeWidth "2", kv .strokeOpacity "0.65"
    ] [])
  if let some f := selectedFull then
    let sensorLeft := (f.summary.x - 5) - (cx - halfW)
    let sensorTop := (f.summary.y - 5) - (cy - halfH)
    if -11 ≤ sensorLeft && sensorLeft < cols && -11 ≤ sensorTop && sensorTop < rows then
      overlayNodes := overlayNodes.push (el .rect [
        kv .x (toString (sensorLeft * tilePx)),
        kv .y (toString (sensorTop * tilePx)),
        kv .width (toString (11 * tilePx)),
        kv .height (toString (11 * tilePx)),
        kv .fill "none", kv .stroke "#79c0ff", kv .strokeWidth "1.5", kv .strokeDasharray "4 3",
        kv .strokeOpacity "0.75"
      ] [])
      for idx in [:121] do
        let extra := f.tileExtra[idx]?.getD 0
        if extra > 0 then
          let ox := sensorLeft + (idx % 11 : Nat)
          let oy := sensorTop + (idx / 11 : Nat)
          if 0 ≤ ox && ox < cols && 0 ≤ oy && oy < rows then
            let px := ox.toNat * tilePx + tilePx / 2
            let py := oy.toNat * tilePx + tilePx / 2
            if extra % 2 == 1 then
              overlayNodes := overlayNodes.push (el .circle [
                kv .cx (toString px), kv .cy (toString py), kv .r "3.5", kv .fill "#f0883e"
              ] [])
            if (extra / 2) % 2 == 1 then
              overlayNodes := overlayNodes.push (el .circle [
                kv .cx (toString px), kv .cy (toString py), kv .r "4", kv .fill "#c68b59",
                kv .stroke "#ffffff", kv .strokeWidth "1"
              ] [])
    if f.gkind == 1 then
      let tx := f.gx - (cx - halfW)
      let ty := f.gy - (cy - halfH)
      if 0 ≤ tx && tx < cols && 0 ≤ ty && ty < rows then
        let px := tx.toNat * tilePx + tilePx / 2
        let py := ty.toNat * tilePx + tilePx / 2
        overlayNodes := overlayNodes.push (el .circle [
          kv .cx (toString px), kv .cy (toString py), kv .r "9",
          kv .fill "none", kv .stroke "#ffd24a", kv .strokeWidth "2.5"
        ] [])
        overlayNodes := overlayNodes.push (el .circle [
          kv .cx (toString px), kv .cy (toString py), kv .r "3.5", kv .fill "#ffd24a"
        ] [])
      else
        let clampedX := max 24 (min (svgW - 24 : Int) (tx * tilePx))
        let clampedY := max 24 (min (svgH - 24 : Int) (ty * tilePx))
        overlayNodes := overlayNodes.push (el .circle [
          kv .cx (toString clampedX), kv .cy (toString clampedY), kv .r "10",
          kv .fill "#211b0b", kv .stroke "#ffd24a", kv .strokeWidth "2"
        ] [])
        overlayNodes := overlayNodes.push (el .text [
          kv .x (toString clampedX), kv .y (toString (clampedY + 4)),
          kv .fill "#ffd24a", kv .fontSize "11", kv .fontWeight "700", kv .textAnchor "middle"
        ] [txt "★"])
  let agentPx : Int := halfW * tilePx + tilePx / 2
  let agentPy : Int := halfH * tilePx + tilePx / 2
  overlayNodes := overlayNodes.push (el .circle [
    kv .cx (toString agentPx), kv .cy (toString agentPy), kv .r "7",
    kv .fill "#ffffff", kv .stroke "#080b10", kv .strokeWidth "2"
  ] [])
  overlayNodes := overlayNodes.push (el .polygon [
    kv .points (facingArrowPoints agentPx agentPy summary.facing),
    kv .fill "#080b10"
  ] [])
  return el .svg [
    kv .cls "stage-svg",
    kv .viewBox s!"0 0 {svgW} {svgH}",
    kv .role "img",
    kv .ariaLabel "Aerial world map around the agent"
  ] (
    [el .rect [kv .x "0", kv .y "0", kv .width (toString svgW), kv .height (toString svgH),
      kv .fill "#0a0e14"] []] ++
    terrainNodes.toList ++ overlayNodes.toList
  )

private def renderSensorSvg (frame : Option ServerFrame) (emptyCaption : String) : Node := Id.run do
  let tilePx : Nat := 18
  let sidePx := 11 * tilePx
  let mut nodes : Array Node := #[
    el .rect [kv .x "0", kv .y "0", kv .width (toString sidePx), kv .height (toString sidePx),
      kv .fill "#080b10"] []
  ]
  match frame with
  | none =>
    nodes := nodes.push (el .text [
      kv .x (toString (sidePx / 2)), kv .y (toString (sidePx / 2 + 4)),
      kv .fill "#7d8997", kv .fontSize "10", kv .textAnchor "middle"
    ] [txt emptyCaption])
  | some f =>
    for idx in [:121] do
      let rx := idx % 11
      let ry := idx / 11
      let kind := f.tiles[idx]?.getD 255
      let extra := f.tileExtra[idx]?.getD 0
      nodes := nodes.push (el .rect [
        kv .x (toString (rx * tilePx)), kv .y (toString (ry * tilePx)),
        kv .width (toString (tilePx - 1)), kv .height (toString (tilePx - 1)),
        kv .fill (terrainHex kind)
      ] [])
      if extra % 2 == 1 then
        nodes := nodes.push (el .circle [
          kv .cx (toString (rx * tilePx + 9)), kv .cy (toString (ry * tilePx + 9)),
          kv .r "4", kv .fill "#f0883e"
        ] [])
      if (extra / 2) % 2 == 1 then
        nodes := nodes.push (el .circle [
          kv .cx (toString (rx * tilePx + 9)), kv .cy (toString (ry * tilePx + 9)),
          kv .r "5", kv .fill "#c68b59", kv .stroke "#fff", kv .strokeWidth "1"
        ] [])
    let center : Int := 5 * tilePx + 9
    nodes := nodes.push (el .circle [
      kv .cx (toString center), kv .cy (toString center), kv .r "6",
      kv .fill "#ffffff", kv .stroke "#080b10", kv .strokeWidth "1.5"
    ] [])
    nodes := nodes.push (el .polygon [
      kv .points (facingArrowPoints center center f.summary.facing),
      kv .fill "#080b10"
    ] [])
  return el .svg [
    kv .cls "block world-svg",
    kv .viewBox s!"0 0 {sidePx} {sidePx}",
    kv .role "img",
    kv .ariaLabel "11 by 11 agent sensor window"
  ] nodes.toList

private def renderWorldOverviewSvg (world : Option ((key : MapKey) × WorldMemory key))
    (summary : Option FrameSummary) (selectedFull : Option ServerFrame)
    (emptyCaption : String) : Node := Id.run do
  let grid : Nat := 40
  let cellPx : Nat := 5
  let sidePx := grid * cellPx
  let mut nodes : Array Node := #[
    el .rect [kv .x "0", kv .y "0", kv .width (toString sidePx), kv .height (toString sidePx),
      kv .fill "#080b10"] []
  ]
  match world with
  | none =>
    nodes := nodes.push (el .text [
      kv .x (toString (sidePx / 2)), kv .y (toString (sidePx / 2 + 4)),
      kv .fill "#7d8997", kv .fontSize "10", kv .textAnchor "middle"
    ] [txt emptyCaption])
  | some ⟨key, mem⟩ =>
    let side := key.side.val
    for gy in [:grid] do
      let wy := gy * side / grid
      for gx in [:grid] do
        let wx := gx * side / grid
        if let some mapIdx := mapIndex key.side wx wy then
          let byte := mem.observations.bytes[mapIdx.val]'(by
            rw [mem.observations.size]; exact mapIdx.isLt)
          if byte != 255 then
            nodes := nodes.push (el .rect [
              kv .x (toString (gx * cellPx)), kv .y (toString (gy * cellPx)),
              kv .width (toString cellPx), kv .height (toString cellPx),
              kv .fill (terrainHex byte.toNat)
            ] [])
    if let some f := selectedFull then
      if f.gkind == 1 && f.gx ≥ 0 && f.gy ≥ 0 then
        let tx := min (sidePx - 3) (f.gx.toNat * sidePx / side)
        let ty := min (sidePx - 3) (f.gy.toNat * sidePx / side)
        nodes := nodes.push (el .circle [
          kv .cx (toString tx), kv .cy (toString ty), kv .r "4",
          kv .fill "none", kv .stroke "#ffd24a", kv .strokeWidth "1.5"
        ] [])
    if let some s := summary then
      if s.x ≥ 0 && s.y ≥ 0 then
        let ax := min (sidePx - 3) (s.x.toNat * sidePx / side)
        let ay := min (sidePx - 3) (s.y.toNat * sidePx / side)
        nodes := nodes.push (el .circle [
          kv .cx (toString ax), kv .cy (toString ay), kv .r "3.5",
          kv .fill "#ffffff", kv .stroke "#080b10", kv .strokeWidth "1"
        ] [])
  return el .svg [
    kv .cls "block world-svg",
    kv .viewBox s!"0 0 {sidePx} {sidePx}",
    kv .role "img",
    kv .ariaLabel "Overview of explored world tiles"
  ] nodes.toList

private def renderRibbonSvg (summaries : List FrameSummary) (cursorIdx : Option Nat) : Node := Id.run do
  let width : Nat := 1120
  let height : Nat := 54
  let mut nodes : Array Node := #[
    el .rect [kv .x "0", kv .y "0", kv .width (toString width), kv .height (toString height),
      kv .fill "#080b10"] []
  ]
  let n := summaries.length
  if n == 0 then
    nodes := nodes.push (el .text [
      kv .x "560", kv .y "31", kv .fill "#7d8997", kv .fontSize "11", kv .textAnchor "middle"
    ] [txt "No buffered frames yet — start the core to observe temporal options."])
  else
    let arr := summaries.toArray
    let mut prevGoal : Option Nat := none
    for idx in [:arr.size] do
      if h : idx < arr.size then
        let s := arr[idx]
        let x0 := idx * width / n
        let x1 := max (x0 + 1) ((idx + 1) * width / n)
        let w := x1 - x0
        if s.skill < 3 then
          let rowY := 12 + s.skill * 11
          nodes := nodes.push (el .rect [
            kv .x (toString x0), kv .y (toString rowY),
            kv .width (toString w), kv .height "9",
            kv .fill (optionColor s.skill)
          ] [])
        else
          nodes := nodes.push (el .rect [
            kv .x (toString x0), kv .y "24",
            kv .width (toString w), kv .height "5",
            kv .fill "#242c38"
          ] [])
        if s.optionStart < 3 then
          nodes := nodes.push (el .line [
            kv .x1 (toString x0), kv .y1 "2", kv .x2 (toString x0), kv .y2 "10",
            kv .stroke (optionColor s.optionStart), kv .strokeWidth "1.5"
          ] [])
        if s.optionEndSkill < 3 then
          nodes := nodes.push (el .line [
            kv .x1 (toString x0), kv .y1 "44", kv .x2 (toString x0), kv .y2 "52",
            kv .stroke (optionColor s.optionEndSkill), kv .strokeWidth "1.5"
          ] [])
        if let some g := prevGoal then
          if g != s.goal then
            nodes := nodes.push (el .line [
              kv .x1 (toString x0), kv .y1 "0", kv .x2 (toString x0), kv .y2 (toString height),
              kv .stroke "#bc8cff", kv .strokeWidth "1.2", kv .strokeOpacity "0.8"
            ] [])
        prevGoal := some s.goal
    if let some idx := cursorIdx then
      let cx := idx * width / n
      nodes := nodes.push (el .line [
        kv .x1 (toString cx), kv .y1 "0", kv .x2 (toString cx), kv .y2 (toString height),
        kv .stroke "#ffffff", kv .strokeWidth "2"
      ] [])
  return el .svg [
    kv .cls "block", kv .viewBox s!"0 0 {width} {height}",
    kv .role "img", kv .ariaLabel "Options execution ribbon across buffered frames"
  ] nodes.toList

private def renderDivergingBarsSvg (names : Array String) (values : Array Scalar)
    (probs : Array Scalar) (aria : String) : Node := Id.run do
  let rowH : Nat := 18
  let height := max 40 (names.size * rowH + 8)
  let width : Nat := 360
  let labelW : Nat := 104
  let barArea : Nat := 176
  let midX := labelW + barArea / 2
  let mut maxAbs : Nat := 100000
  for v in values do
    if let some s := v.scaled6 then
      if s.natAbs > maxAbs then maxAbs := s.natAbs
  let mut nodes : Array Node := #[
    el .rect [kv .x "0", kv .y "0", kv .width (toString width), kv .height (toString height),
      kv .fill "#080b10"] [],
    el .line [kv .x1 (toString midX), kv .y1 "2", kv .x2 (toString midX), kv .y2 (toString (height - 2)),
      kv .stroke "#242c38", kv .strokeWidth "1"] []
  ]
  for idx in [:names.size] do
    let name := names[idx]?.getD s!"#{idx}"
    let val := values[idx]?.getD .nonFinite
    let prob := probs[idx]?.getD .nonFinite
    let y := idx * rowH + 4
    nodes := nodes.push (el .text [
      kv .x "6", kv .y (toString (y + 12)), kv .fill "#8b97a6", kv .fontSize "10"
    ] [txt name])
    match val.scaled6 with
    | some s =>
      let len := min (barArea / 2 - 2) (s.natAbs * (barArea / 2 - 2) / maxAbs)
      let (bx, fill) := if s ≥ 0 then (midX, "#7ee787") else (midX - len, "#ff7b72")
      nodes := nodes.push (el .rect [
        kv .x (toString bx), kv .y (toString (y + 3)),
        kv .width (toString (max 1 len)), kv .height "11", kv .fill fill
      ] [])
    | none =>
      nodes := nodes.push (el .text [
        kv .x (toString midX), kv .y (toString (y + 12)), kv .fill "#ff7b72", kv .fontSize "9",
        kv .textAnchor "middle"
      ] [txt "⚠"])
    let rightText := val.formatCompact 2 ++ " (" ++
      (match prob.scaled6 with
        | some p => formatDecimal1 (min 1000 (p.natAbs / 1000)) ++ "%"
        | none => "⚠") ++ ")"
    nodes := nodes.push (el .text [
      kv .x (toString (width - 6)), kv .y (toString (y + 12)),
      kv .fill "#e6edf3", kv .fontSize "9.5", kv .textAnchor "end"
    ] [txt rightText])
  return el .svg [
    kv .cls "block", kv .viewBox s!"0 0 {width} {height}",
    kv .role "img", kv .ariaLabel aria
  ] nodes.toList

private def renderAgreementHistorySvg (ag : AgreementSnapshot) : Node := Id.run do
  let width : Nat := 400
  let height : Nat := 96
  let mut points : List (Nat × Nat) := []
  for idx in [:ag.historyClock.size] do
    if let some clk := ag.historyClock[idx]?.join then
      if let some sc := ag.historyScore[idx]?.join then
        points := (clk, sc) :: points
  let ordered := points.reverse
  let mut nodes : Array Node := #[
    el .rect [kv .x "0", kv .y "0", kv .width (toString width), kv .height (toString height),
      kv .fill "#080b10"] [],
    el .line [kv .x1 "8", kv .y1 "86", kv .x2 "392", kv .y2 "86", kv .stroke "#242c38", kv .strokeWidth "1"] [],
    el .line [kv .x1 "8", kv .y1 "10", kv .x2 "392", kv .y2 "10", kv .stroke "#242c38", kv .strokeDasharray "3 3"] []
  ]
  if ordered.isEmpty then
    nodes := nodes.push (el .text [
      kv .x "200", kv .y "52", kv .fill "#7d8997", kv .fontSize "10.5", kv .textAnchor "middle"
    ] [txt "Waiting for settled predictive agreement history."])
  else
    let n := ordered.length
    let scale := max 1 ag.scale
    let coords := (List.range n).filterMap fun i =>
      match ordered[i]? with
      | some (_, sc) =>
        let px := if n ≤ 1 then 200 else 10 + i * 380 / (n - 1)
        let py := 86 - min 76 (sc * 76 / scale)
        some s!"{px},{py}"
      | none => none
    if coords.length ≥ 2 then
      nodes := nodes.push (el .polyline [
        kv .points (String.intercalate " " coords),
        kv .fill "none", kv .stroke "#7ee787", kv .strokeWidth "2"
      ] [])
    else if let some (_, sc) := ordered.head? then
      let py := 86 - min 76 (sc * 76 / scale)
      nodes := nodes.push (el .circle [
        kv .cx "200", kv .cy (toString py), kv .r "3.5", kv .fill "#7ee787"
      ] [])
  return el .svg [
    kv .cls "block", kv .viewBox s!"0 0 {width} {height}",
    kv .role "img", kv .ariaLabel "Predictive agreement score over lifetime buckets"
  ] nodes.toList

private def renderPlasticitySvg (samples : List HistorySample) : Node := Id.run do
  let width : Nat := 320
  let height : Nat := 110
  let mut nodes : Array Node := #[
    el .rect [kv .x "0", kv .y "0", kv .width (toString width), kv .height (toString height),
      kv .fill "#080b10"] []
  ]
  for exp in [(-6 : Int), -4, -2, 0] do
    let y : Int := 100 - ((exp + 7) * 90 / 7)
    nodes := nodes.push (el .line [
      kv .x1 "28", kv .y1 (toString y), kv .x2 "314", kv .y2 (toString y),
      kv .stroke "#1b222c", kv .strokeWidth "1"
    ] [])
    nodes := nodes.push (el .text [
      kv .x "24", kv .y (toString (y + 3)), kv .fill "#7d8997", kv .fontSize "8.5", kv .textAnchor "end"
    ] [txt s!"1e{exp}"])
  let n := samples.length
  if n == 0 then
    nodes := nodes.push (el .text [
      kv .x "170", kv .y "58", kv .fill "#7d8997", kv .fontSize "10", kv .textAnchor "middle"
    ] [txt "Waiting for step-size history."])
  else
    let series : List (String × String × (HistorySample → Option Decimal)) := [
      ("#79c0ff", "", fun s => s.aDem),
      ("#7ee787", "5 2", fun s => s.aCtl),
      ("#ffd24a", "2 2", fun s => s.aMeta),
      ("#f0883e", "6 2 2 2", fun s => s.aOpt)
    ]
    for (color, dash, proj) in series do
      let coords := (List.range n).filterMap fun i =>
        match samples[i]?.bind proj |>.bind Decimal.log10Scaled100 with
        | some logVal =>
          let clamped := max (-700 : Int) (min 0 logVal)
          let px := if n ≤ 1 then 170 else 30 + i * 282 / (n - 1)
          let py : Int := 100 - ((clamped + 700) * 90 / 700)
          some s!"{px},{py}"
        | none => none
      if coords.length ≥ 2 then
        let attrs := [kv .points (String.intercalate " " coords), kv .fill "none",
          kv .stroke color, kv .strokeWidth "1.6"] ++
          (if dash.isEmpty then [] else [kv .strokeDasharray dash])
        nodes := nodes.push (el .polyline attrs [])
  return el .svg [
    kv .cls "block", kv .viewBox s!"0 0 {width} {height}",
    kv .role "img", kv .ariaLabel "Log-scale step size trajectory across learner families"
  ] nodes.toList

private def renderSurpriseSvg (samples : List HistorySample) : Node := Id.run do
  let width : Nat := 360
  let height : Nat := 72
  let mut nodes : Array Node := #[
    el .rect [kv .x "0", kv .y "0", kv .width (toString width), kv .height (toString height),
      kv .fill "#080b10"] []
  ]
  let vals : List Int := samples.filterMap fun s => s.surprise.bind (·.scaled? 6)
  if vals.isEmpty then
    nodes := nodes.push (el .text [
      kv .x "180", kv .y "40", kv .fill "#7d8997", kv .fontSize "10", kv .textAnchor "middle"
    ] [txt "Waiting for adjacent world steps to measure TD surprise."])
  else
    let maxV := vals.foldl (fun acc v => max acc v.natAbs) 10000
    let n := vals.length
    let coords := (List.range n).filterMap fun i =>
      match vals[i]? with
      | some v =>
        let px := if n ≤ 1 then 180 else 8 + i * 344 / (n - 1)
        let py := 64 - min 56 (v.natAbs * 56 / maxV)
        some s!"{px},{py}"
      | none => none
    if coords.length ≥ 2 then
      nodes := nodes.push (el .polyline [
        kv .points (String.intercalate " " coords),
        kv .fill "none", kv .stroke "#bc8cff", kv .strokeWidth "1.8"
      ] [])
  return el .svg [
    kv .cls "block", kv .viewBox s!"0 0 {width} {height}",
    kv .role "img", kv .ariaLabel "Mean absolute TD surprise across sampled steps"
  ] nodes.toList

private def renderLifetimeHistorySvg (frame : ServerFrame) : Node := Id.run do
  let width : Nat := 400
  let height : Nat := 84
  let mut errPts : List (Nat × Nat) := []
  let mut rewPts : List (Nat × Int) := []
  for idx in [:64] do
    let ec := frame.lifetimeErrorHistoryCount[idx]?.getD 0
    if ec > 0 then
      if let some es := (frame.lifetimeErrorHistorySum[idx]?.getD .nonFinite).scaled6 then
        errPts := (idx, es.natAbs / ec) :: errPts
    let rc := frame.lifetimeRewardHistoryCount[idx]?.getD 0
    if rc > 0 then
      if let some rs := (frame.lifetimeRewardHistorySum[idx]?.getD .nonFinite).scaled6 then
        rewPts := (idx, rs / (rc : Int)) :: rewPts
  let errOrdered := errPts.reverse
  let rewOrdered := rewPts.reverse
  let mut nodes : Array Node := #[
    el .rect [kv .x "0", kv .y "0", kv .width (toString width), kv .height (toString height),
      kv .fill "#080b10"] []
  ]
  if errOrdered.isEmpty && rewOrdered.isEmpty then
    nodes := nodes.push (el .text [
      kv .x "200", kv .y "46", kv .fill "#7d8997", kv .fontSize "10", kv .textAnchor "middle"
    ] [txt "Waiting for lifetime history buckets."])
  else
    let maxErr := errOrdered.foldl (fun a p => max a p.2) 1000
    let errCoords := errOrdered.map fun (idx, v) =>
      let px := 10 + idx * 380 / 63
      let py := 74 - min 64 (v * 64 / maxErr)
      s!"{px},{py}"
    if errCoords.length ≥ 2 then
      nodes := nodes.push (el .polyline [
        kv .points (String.intercalate " " errCoords),
        kv .fill "none", kv .stroke "#79c0ff", kv .strokeWidth "1.8"
      ] [])
    let maxRew := rewOrdered.foldl (fun a p => max a p.2.natAbs) 1000
    let rewCoords := rewOrdered.map fun (idx, v) =>
      let px := 10 + idx * 380 / 63
      let py : Int := 42 - (max (-30 : Int) (min 30 (v * 30 / (maxRew : Int))))
      s!"{px},{py}"
    if rewCoords.length ≥ 2 then
      nodes := nodes.push (el .polyline [
        kv .points (String.intercalate " " rewCoords),
        kv .fill "none", kv .stroke "#7ee787", kv .strokeWidth "1.6", kv .strokeDasharray "4 2"
      ] [])
  return el .svg [
    kv .cls "block", kv .viewBox s!"0 0 {width} {height}",
    kv .role "img", kv .ariaLabel "Lifetime error and reward across logarithmic step buckets"
  ] nodes.toList

private def learnerDetailNode (title : String) (alphas : Array Scalar) (credits : Array Nat) : Node :=
  let lines := (List.range alphas.size).map fun idx =>
    let a := (alphas[idx]?.getD .nonFinite).formatCompact 4
    let c := formatNatCommas (credits[idx]?.getD 0)
    s!"#{idx + 1}: α={a} · credit={c}"
  el .details [kv .cls "learner-detail"] [
    el .summary [] [txt s!"{title} ({alphas.size} heads)"],
    el .pre [] [txt (String.intercalate "\n" lines)]
  ]

inductive GoalHeadlineState where
  | invalid
  | waiting (cycle : Nat) (goalCount : Nat) (stopped : Bool)
  | firstIncomplete (score : Nat) (cycle achieved resolved goalCount : Nat) (stopped : Bool)
  | completed (score : Nat) (completedCycle completedAchieved goalCount : Nat)
      (currentCycle currentResolved currentAchieved : Nat) (stopped : Bool)
  | unavailable
  deriving DecidableEq, BEq

def classifyGoalHeadline (gp : GoalProgressSnapshot) (stopped : Bool) : GoalHeadlineState :=
  if gp.invalid then .invalid
  else if gp.goalCount == 0 then .unavailable
  else
    match gp.completedCycle, gp.completedAchieved, gp.score with
    | some compCycle, some compAch, some sc =>
      .completed sc compCycle compAch gp.goalCount gp.cycle gp.resolved gp.achieved stopped
    | none, none, _ =>
      if gp.resolved == 0 then .waiting gp.cycle gp.goalCount stopped
      else match gp.score with
        | some sc => .firstIncomplete sc gp.cycle gp.achieved gp.resolved gp.goalCount stopped
        | none => .unavailable
    | _, _, _ => .unavailable

theorem classifyGoalHeadline_first_incomplete (gp : GoalProgressSnapshot) (stopped : Bool) (sc : Nat)
    (hValid : gp.invalid = false) (hGoals : 0 < gp.goalCount)
    (hNoCompCycle : gp.completedCycle = none) (hNoCompAch : gp.completedAchieved = none)
    (hResolved : 0 < gp.resolved) (hScore : gp.score = some sc) :
    classifyGoalHeadline gp stopped =
      .firstIncomplete sc gp.cycle gp.achieved gp.resolved gp.goalCount stopped := by
  have hGoalsNe : (gp.goalCount == 0) = false := beq_false_of_ne (Nat.ne_of_gt hGoals)
  have hResNe : (gp.resolved == 0) = false := beq_false_of_ne (Nat.ne_of_gt hResolved)
  simp [classifyGoalHeadline, hValid, hGoalsNe, hNoCompCycle, hNoCompAch, hResNe, hScore]

theorem classifyGoalHeadline_waiting (gp : GoalProgressSnapshot) (stopped : Bool)
    (hValid : gp.invalid = false) (hGoals : 0 < gp.goalCount)
    (hNoCompCycle : gp.completedCycle = none) (hNoCompAch : gp.completedAchieved = none)
    (hResolved : gp.resolved = 0) :
    classifyGoalHeadline gp stopped = .waiting gp.cycle gp.goalCount stopped := by
  have hGoalsNe : (gp.goalCount == 0) = false := beq_false_of_ne (Nat.ne_of_gt hGoals)
  simp [classifyGoalHeadline, hValid, hGoalsNe, hNoCompCycle, hNoCompAch, hResolved]

theorem classifyGoalHeadline_completed (gp : GoalProgressSnapshot) (stopped : Bool)
    (compCycle compAch sc : Nat)
    (hValid : gp.invalid = false) (hGoals : 0 < gp.goalCount)
    (hCompCycle : gp.completedCycle = some compCycle)
    (hCompAch : gp.completedAchieved = some compAch)
    (hScore : gp.score = some sc) :
    classifyGoalHeadline gp stopped =
      .completed sc compCycle compAch gp.goalCount gp.cycle gp.resolved gp.achieved stopped := by
  have hGoalsNe : (gp.goalCount == 0) = false := beq_false_of_ne (Nat.ne_of_gt hGoals)
  simp [classifyGoalHeadline, hValid, hGoalsNe, hCompCycle, hCompAch, hScore]

private structure GoalHeadlineDisplay where
  value : String
  scoreBar : Option Nat
  population : String
  tileCaption : String
  currentProgress : String

private def goalHeadlineDisplay (gp : GoalProgressSnapshot) (stopped : Bool) : GoalHeadlineDisplay :=
  let stopTag := if stopped then " · stopped" else ""
  match classifyGoalHeadline gp stopped with
  | .invalid =>
    { value := "invalid"
      scoreBar := none
      population := "Invalid outcome order — score suppressed"
      tileCaption := "Outcome order invalid"
      currentProgress := s!"Current pass {gp.cycle + 1}{stopTag}: accounting suppressed" }
  | .waiting cycle goalCount _ =>
    { value := "Waiting"
      scoreBar := none
      population := s!"Waiting for first resolved goal (0/{goalCount} resolved)"
      tileCaption := s!"Waiting · Pass {cycle + 1}{stopTag}"
      currentProgress := s!"Current pass {cycle + 1}{stopTag}: 0/{goalCount} resolved (0.0%)" }
  | .firstIncomplete sc cycle achieved resolved goalCount _ =>
    let pct := formatPercent1 resolved goalCount
    { value := formatPermilleScore (some sc) 1000
      scoreBar := some sc
      population := s!"{achieved}/{goalCount} achieved so far · first pass incomplete (unresolved goals unknown)"
      tileCaption := s!"so far · first pass incomplete ({achieved}/{goalCount})"
      currentProgress := s!"Current pass {cycle + 1}{stopTag}: {resolved}/{goalCount} resolved ({pct})" }
  | .completed sc compCycle compAch goalCount curCycle curResolved curAchieved _ =>
    let pct := formatPercent1 curResolved goalCount
    let completedCount := compCycle + 1
    let progressLine :=
      if curCycle > compCycle then
        s!"Current pass {curCycle + 1}{stopTag}: {curResolved}/{goalCount} resolved ({pct}) · {curAchieved} achieved so far · {completedCount} completed"
      else
        s!"Current pass {curCycle + 1}{stopTag}: {curResolved}/{goalCount} resolved ({pct}) · {completedCount} completed"
    { value := formatPermilleScore (some sc) 1000
      scoreBar := some sc
      population := s!"Pass {compCycle + 1} complete · {compAch}/{goalCount} achieved"
      tileCaption := s!"Pass {compCycle + 1} complete · {compAch}/{goalCount}"
      currentProgress := progressLine }
  | .unavailable =>
    { value := "—"
      scoreBar := none
      population := "Goal progress unavailable"
      tileCaption := "Unavailable"
      currentProgress := "Current pass progress unavailable" }

private def renderGoalSidebar (agOpt : Option AgreementSnapshot) (selectedIsEarlier : Bool) : Node :=
  match agOpt with
  | none =>
    el .div [kv .cls "panel goal-summary"] [
      el .h2 [] [txt "Goal achievement"],
      el .div [kv .cls "agreement-primary goal-primary"] [
        el .strong [] [txt "Waiting"],
        el .p [kv .cls "lede"] [txt "No curriculum snapshot yet. Start the core to observe goal achievement."]
      ]
    ]
  | some ag =>
    let gp := ag.goalProgress
    let disp := goalHeadlineDisplay gp ag.stopped
    let scoreCls := if disp.scoreBar.isSome then "has-score" else ""
    let goalRows := (List.range gp.goalCount).map fun idx =>
      let nm := gp.curriculumNames[idx]?.getD s!"Goal {idx + 1}"
      let failed := gp.curriculumFailed[idx]?.getD 0
      let succ := gp.curriculumSuccessSteps[idx]?.join
      let isCur := idx == gp.activeGoal
      let (stCls, statusText) :=
        match succ with
        | some steps => ("st ok", s!"solved in {formatNatCommas steps} steps")
        | none =>
          if isCur then ("st run", s!"attempt {gp.attempt + 1}/{gp.attemptCap}")
          else if failed ≥ gp.attemptCap then ("st no", s!"{failed} failed")
          else ("st wait", if failed > 0 then s!"{failed} failed" else "queued")
      el .div [kv .cls (if isCur then "goal cur" else "goal")] [
        el .span [kv .cls stCls] [],
        el .span [kv .cls "nm"] [txt s!"{idx + 1}. {nm}"],
        el .span [kv .cls "at"] [txt statusText]
      ]
    el .div [kv .cls "panel goal-summary"] [
      el .h2 [] [txt "Goal achievement"],
      whenNode selectedIsEarlier
        (el .div [kv .cls "scope-note"] [txt "Scope: latest core process snapshot (independent of paused frame)."]),
      el .div [kv .cls "agreement-primary goal-primary"] [
        el .strong (if scoreCls.isEmpty then [] else [kv .cls scoreCls]) [txt disp.value],
        match disp.scoreBar with
        | some sc => el .progress [kv .value (toString sc), kv .max "1000"] []
        | none => .empty,
        el .div [kv .cls "lede"] [txt disp.population]
      ],
      el .div [kv .cls "scope-note"] [txt disp.currentProgress],
      el .details [kv .cls "cite"] [
        el .summary [] [txt "scope & citation"],
        el .div [kv .cls "body"] [
          txt "Truncated permille (1000 * achieved / goals) over the latest completed curriculum pass once available, or achieved/assigned so far during an incomplete first pass (unresolved goals unknown), reading directly from Acorn.Host.Viewer.GoalAchievement without browser-side recomputation."
        ]
      ],
      el .div [kv .id "goals"] goalRows
    ]

private def renderCycleBucketTable (frame : ServerFrame) : Node :=
  let famNames := frame.goalFamilyNames
  let bins := BrowserConstant.cycleBins.value
  let activeBins := (List.range bins).filter fun b =>
    (List.range 4).any fun f => (frame.lifetimeCycleAttempts[f * bins + b]?.getD 0) > 0
  if activeBins.isEmpty then
    el .div [kv .cls "lede"] [txt "No curriculum cycle attempts recorded yet."]
  else
    let rows := activeBins.map fun b =>
      let first := BrowserNat.cycleFirst.eval (fun _ => b)
      let last := BrowserNat.cycleLast.eval (fun _ => b)
      let label := if first == last then s!"c{first}" else s!"c{first}–{last}"
      let cells := (List.range 4).map fun f =>
        let att := frame.lifetimeCycleAttempts[f * bins + b]?.getD 0
        let suc := frame.lifetimeCycleSuccesses[f * bins + b]?.getD 0
        el .td [] [txt (if att == 0 then "—" else s!"{suc}/{att}")]
      el .tr [] (el .td [] [txt label] :: cells)
    let headers := el .th [] [txt "Cycle"] :: (List.range 4).map fun f =>
      el .th [] [txt (famNames[f]?.getD s!"F{f}")]
    el .table [kv .cls "data"] [
      el .thead [] [el .tr [] headers],
      el .tbody [] rows
    ]

def renderViewerPage (snapshot : BroadcastSnapshot) (query : ViewQuery)
    (token : String) (notice : Option ControlNotice) (nowMonoMs : Nat) : Document :=
  let lifecycle := snapshot.lifecycle
  let phase := lifecycle.phaseValue
  let label := phase.runLabel
  let observer := snapshot.observer
  let summaries := observer.summaries.values
  let bufferedCount := summaries.length
  let latestFrame := observer.latest
  let proj := projectDisplay summaries latestFrame query
  let clampedIdx := proj.clampedIdx
  let displaySummary := proj.displaySummary
  let curOneBased := (clampedIdx.map (· + 1)).getD 1
  let isRunning := match phase with | .running _ => true | _ => false
  let detailReason := match snapshot.detail with
    | some d => controlReason lifecycle d
    | none => ""
  let termWarning := snapshot.detail.bind (controlWarning lifecycle)
  let tailLines := match snapshot.detail with
    | some d => controlTail lifecycle d
    | none => []
  let clearDisabled := snapshot.detail.bind (·.clearDisabled)
  let unaskedStop := match snapshot.detail with
    | some d => unaskedStops.contains d.transition
    | none => false
  let liveness := observer.streamLiveness lifecycle unaskedStop snapshot.runningSinceMonoMs nowMonoMs
  let refreshSecs := effectiveRefreshSeconds phase query
  let refreshTarget := { query with
    watch := match phase with | .starting _ | .stopping _ | .archiving => query.watch | _ => false
  }
  let headNodes : List Node :=
    [vd .metaTag [kv .charset "UTF-8"],
     vd .metaTag [kv .name "viewport", kv .content "width=device-width, initial-scale=1.0"],
     el .title [] [txt "OAK — an agent in a big world"],
     vd .link [kv .rel "stylesheet", kv .href "/style.css"]] ++
    (match refreshSecs with
      | some secs =>
        [vd .metaTag [kv .httpEquiv "refresh", kv .content s!"{secs};url={refreshTarget.href}"]]
      | none => [])
  let worldStat := match displaySummary with
    | some s => formatNatCommas s.worldStep
    | none => "—"
  let lifeStat := match displaySummary with
    | some s => formatNatCommas s.lifetimeStep
    | none => "—"
  let worldStatLabel := if proj.selectedIsEarlier then s!"world · #{curOneBased}" else "world"
  let lifeStatLabel := if proj.selectedIsEarlier then s!"lifetime · #{curOneBased}" else "agent lifetime"
  let rateStat :=
    if !isRunning then "— frames/s"
    else match observer.framesPerSecondTenths nowMonoMs with
      | some tenths => formatNatCommas (tenths / 10) ++ "." ++ toString (tenths % 10) ++ " frames/s"
      | none => "— frames/s"
  let seenStat := match snapshot.world with
    | some ⟨key, mem⟩ =>
      let seen := mem.seen
      let total := key.side.val * key.side.val
      let pct := formatPercent1 seen total
      let suffix := if mem.isIncomplete || snapshot.observation.mapPartial then " (partial)" else ""
      s!"{formatNatCommas seen} / {formatNatCommas total} ({pct}){suffix}"
    | none =>
      match latestFrame with
      | some f =>
        if f.summary.side > mapSideCapacity then
          s!"unretained (side {formatNatCommas f.summary.side} > {formatNatCommas mapSideCapacity})"
        else "—"
      | none => "—"
  let (originWord, originCls, originTitle) := match observer.lastFreshOrigin with
    | some "fresh" => ("fresh", "pill fresh", "Authoritative origin reported by the latest fresh frame.")
    | some "resumed" => ("resumed", "pill resumed", "Authoritative origin reported by the latest fresh frame (checkpoint resumed).")
    | some "cleared" => ("cleared", "pill cleared", "Authoritative origin reported by the latest fresh frame (cleared run).")
    | some other => (other, "pill fresh", "Authoritative origin reported by the latest fresh frame.")
    | none => ("origin unreported", "pill unknown", "No fresh frame has reported this process's origin yet.")
  let idText := s!"{originWord} · {runHex lifecycle.identityValue.run} · ep {lifecycle.identityValue.agentEpoch}"
  let connBadge : String × String :=
    match liveness with
    | .fault exhausted =>
      let fallback := if exhausted then "core stopped — gave up after 3 failed starts in a row"
        else "core stopped — unexpected exit"
      ("dead", if detailReason.isEmpty then fallback else s!"core stopped — {detailReason}")
    | .stale true => ("dead", "stale — no fresh frames")
    | .stale false => ("dead", "stale — no capture received")
    | .live => ("live", "live")
    | .waitingForCapture => ("wait", "awaiting first frame")
    | .busy s => ("wait", s)
    | .idle =>
      if termWarning.isSome then
        ("dead", if detailReason.isEmpty then "core stopped — warning" else s!"core stopped — {detailReason}")
      else ("wait", "core stopped")
  let restartPillAttrs :=
    [kv .cls "pill reset", kv .id "s_restarted"] ++
    (if detailReason.isEmpty then [] else [kv .title detailReason])
  let restartPillText :=
    if isRunning then s!"⟲ restarted after unexpected exit ({lifecycle.failureCount}/{failureLimit})"
    else s!"failed starts: {lifecycle.failureCount}/{failureLimit}"
  let healthPills : List Node :=
    [whenNode (observer.nonFiniteCount > 0)
      (el .span [kv .cls "pill reset", kv .id "s_broken"]
        [txt s!"⚠ non-finite ({observer.nonFiniteCount}: {observer.lastNonFiniteKey.getD "?"})"]),
     whenNode (observer.refusedCount > 0)
      (el .span [kv .cls "pill reset"]
        [txt s!"⚠ refused ({observer.refusedCount})"]),
     whenNode (snapshot.observation.checkpointRefused || termWarning.isSome)
      (el .span [kv .cls "pill reset", kv .id "s_nosave"]
        [txt (termWarning.getD "checkpoint refused")]),
     whenNode (lifecycle.failureCount > 0)
      (el .span restartPillAttrs [txt restartPillText]),
     whenNode notice.isSome
      (el .span [kv .cls "pill reset", kv .id "s_ctlfault"]
        [txt "control fault"])]
  let primaryCmd := if phase == .idle then "start" else "stop"
  let primaryBtnAttrs :=
    [kv .type "submit", kv .id "b_run", kv .cls "ctl"] ++
    (if label.busy then [flg .disabled, kv .title s!"Busy: {label.state}"] else [])
  let clearBtnAttrs :=
    [kv .type "submit", kv .id "b_clear", kv .cls "ctl danger"] ++
    (if label.busy then [flg .disabled, kv .title s!"Busy: {label.state}"]
      else match clearDisabled with
        | some why => [flg .disabled, kv .title why]
        | none => [kv .title "Archive the current run directory and start a fresh agent"])
  let runstateAttrs :=
    [kv .id "runstate", kv .cls s!"runstate {label.style}"] ++
    (if detailReason.isEmpty then [] else [kv .title detailReason])
  let topBar := el .div [kv .id "top"] [
    el .h1 [] [txt "◈ OAK"],
    el .span [kv .cls "pill live", kv .id "evidence-mode"] [txt "LIVE RUN · zero-JS"],
    el .div [kv .cls "stat"] [el .span [kv .cls "k"] [txt worldStatLabel], el .span [kv .cls "v", kv .id "s_world"] [txt worldStat]],
    el .div [kv .cls "stat", kv .title "Total agent steps, restored from its saved checkpoint on resume."]
      [el .span [kv .cls "k"] [txt lifeStatLabel], el .span [kv .cls "v", kv .id "s_life"] [txt lifeStat]],
    el .div [kv .cls "stat", kv .title "Newly admitted fresh capture envelopes per second over the recent 1–2s window."]
      [el .span [kv .cls "k"] [txt "core"], el .span [kv .cls "v", kv .id "s_rate"] [txt rateStat]],
    el .div [kv .cls "stat", kv .title "Retained terrain memory sensed across the current run."]
      [el .span [kv .cls "k"] [txt "seen"], el .span [kv .cls "v", kv .id "s_seen"] [txt seenStat]],
    el .div [kv .id "topright"] [
      el .span [kv .cls originCls, kv .id "agentstate", kv .title originTitle] [txt idText],
      el .div [kv .id "streamhealth"] healthPills,
      el .div [kv .id "runctl"] [
        el .form [kv .method "POST", kv .action "/control/form", kv .cls "ctl-form"]
          ([vd .input [kv .type "hidden", kv .name "token", kv .value token],
            vd .input [kv .type "hidden", kv .name "cmd", kv .value primaryCmd]] ++
            hiddenViewInputs query ++
            [el .button primaryBtnAttrs [txt label.action]]),
        el .form [kv .method "POST", kv .action "/control/form", kv .cls "ctl-form"]
          ([vd .input [kv .type "hidden", kv .name "token", kv .value token],
            vd .input [kv .type "hidden", kv .name "cmd", kv .value "clear"]] ++
            hiddenViewInputs query ++
            [el .button clearBtnAttrs [txt "Clear"]]),
        el .span runstateAttrs [txt label.state]
      ],
      el .span [kv .id "conn", kv .cls connBadge.1] [txt connBadge.2]
    ]
  ]
  let noticeNode := match notice with
    | none => .empty
    | some n =>
      let msg := match n with
        | .forbidden => "Control request refused (invalid or expired session token, or Clear is disabled)."
        | .refused _ reason => s!"Control request could not be applied: {reason}"
        | .unconfirmed reason => s!"Stop durability unconfirmed: {reason}"
      el .div [kv .cls "notice-banner", kv .role "alert"] [
        el .span [] [txt msg],
        el .a [kv .cls "btn", kv .href query.href] [txt "Dismiss"]
      ]
  let showDiagnostic :=
    (phase == .idle || unaskedStop || termWarning.isSome || !tailLines.isEmpty) &&
    (!detailReason.isEmpty || termWarning.isSome || !tailLines.isEmpty)
  let diagFault := unaskedStop || termWarning.isSome
  let lifecycleDiagnosticNode :=
    if !showDiagnostic then .empty
    else
      el .div [kv .id "lifecycle-diagnostic",
        kv .cls (if diagFault then "diag-banner fault" else "diag-banner"),
        kv .role (if diagFault then "alert" else "status")] [
        el .div [kv .cls "diag-head"] [
          txt (if detailReason.isEmpty then s!"Lifecycle: {label.state}"
            else s!"Lifecycle ({label.state}): {detailReason}")
        ],
        match termWarning with
        | some warn => el .div [kv .cls "diag-warn"] [txt s!"⚠ {warn}"]
        | none => .empty,
        whenNode (!tailLines.isEmpty)
          (el .pre [kv .cls "tail"] [txt (String.intercalate "\n" tailLines)])
      ]
  let insideHref := { query with inside := true }.href ++ "#research"
  let welcomeSection := el .section [kv .id "welcome", kv .ariaLabel "Welcome to Acorn"] [
    el .div [] [
      el .h2 [] [txt "Watch an agent find its way."],
      el .p [] [txt "The marker in the center is your agent. The Current goal card above the map says what it is trying to do. For travel goals, look for the gold target or direction arrow."],
      el .p [] [txt "Agent lifetime counts total experience. Current world counts steps since the world restarted. Resume restores saved experience and starts a new world clock."]
    ],
    el .p [] [
      txt "Watch for a while. If the run is stopped, ",
      el .b [] [txt "Start"],
      txt " begins it and resumes saved learning when available; ",
      el .b [] [txt "Stop"],
      txt " finishes the current attempt.",
      el .a [kv .href insideHref] [txt "Explore what's happening inside ↓"]
    ]
  ]
  let (hudGoalLbl, hudGoalText, hudGoalMeta) := match proj.selectedFull, displaySummary with
    | some f, _ =>
      ("current goal",
       goalText f.gkind f.gitem f.gx f.gy f.gn,
       s!"goal {f.summary.goal + 1}/{f.agreement.goalProgress.goalCount} · attempt {f.attempt + 1}/{f.agreement.goalProgress.attemptCap} · tier {f.tier} · cycle {f.summary.cycle + 1}")
    | none, some s =>
      let gName := (observer.agreement.bind (·.goalProgress.curriculumNames[s.goal]?)).getD s!"Goal {s.goal + 1}"
      let gCount := match observer.agreement with | some ag => toString ag.goalProgress.goalCount | none => "?"
      let termTag := (if s.terminal then " · terminal" else "") ++ (if s.done then " · done" else "")
      (s!"goal at frame #{curOneBased}",
       gName,
       s!"goal {s.goal + 1}/{gCount} · cycle {s.cycle + 1}{termTag} (attempt/tier & target coordinates retained for newest frame only)")
    | none, none =>
      ("current goal", "—", "Waiting for frames from acorn-core")
  let hudTod := match displaySummary with
    | some s =>
      if s.dayLength > 0 then
        dayPhaseLabel (BrowserNat.dayPhase.eval (BrowserNat.dayArguments s.worldStep s.dayLength))
      else "—"
    | none => "—"
  let modeLabel :=
    if query.stream then "BMP STREAM · HTML SNAPSHOT"
    else match query.mode, clampedIdx with
      | .paused, some idx =>
        let behind := bufferedCount - 1 - idx
        if behind > 0 then s!"PAUSED #{idx + 1}/{bufferedCount} · {behind} behind newest"
        else s!"PAUSED #{idx + 1}/{bufferedCount} (newest)"
      | _, _ =>
        match liveness with
        | .live =>
          match refreshSecs with
          | some _ => "LIVE (HTML SNAPSHOT)"
          | none => "LIVE · REFRESH OFF"
        | .waitingForCapture => "WAITING FOR FIRST FRAME"
        | .stale _ => "STREAM STALE"
        | .fault _ => "CORE FAILED"
        | .busy s => s.toUpper
        | .idle => if bufferedCount == 0 then "WAITING FOR FIRST FRAME" else "CORE STOPPED"
  let htmlSnapshotDesc := match refreshSecs with
    | some s => s!"as-of HTML snapshot (auto-refreshing every {s}s)"
    | none =>
      if isRunning then "static as-of HTML snapshot (auto-refresh off — reload for updated lifecycle status or metrics)"
      else "as-of HTML snapshot (core not running)"
  let mapSurfaceChild : Node :=
    if query.stream then
      el .div [] [
        el .img [
          kv .cls "stage-img", kv .src "/stream/stage.bmp",
          kv .width "1152", kv .height "640",
          kv .alt "Live zero-JS aerial world map stream"
        ] [],
        el .div [kv .cls "stage-caption"] [
          el .span [] [txt "Stage image: live multipart/x-mixed-replace BMP stream (250 ms cadence; shows unavailable, stopped, failed, or stale banner)."],
          el .span [] [txt s!"Controls, badge & panels: {htmlSnapshotDesc}."]
        ]
      ]
    else
      match displaySummary with
      | some s =>
        el .div [] [
          renderStageSvg snapshot.world proj.selectedFull s proj.trailSummaries,
          whenNode proj.selectedIsEarlier
            (el .div [kv .cls "stage-caption"] [
              el .span [] [txt s!"Historical frame #{curOneBased}: pose, facing, trail up to frame #{curOneBased}, and daylight over retained run terrain memory."],
              el .span [] [txt "11 × 11 sensor overlay, transient entities, and target coordinates are retained for newest frame only."]
            ])
        ]
      | none =>
        el .div [kv .cls "empty-stage"] [
          el .h3 [] [txt "No frames from this run yet"],
          el .p [] [txt (match liveness with
            | .waitingForCapture => "Core is running — waiting for the first fresh telemetry frame."
            | .stale false => "Core is running, but no fresh telemetry capture arrived within the stale window."
            | .fault _ => "Core exited before emitting a telemetry frame; see the lifecycle diagnostic above."
            | .busy s => s!"Core is {s}."
            | _ => "Core is stopped. Press Start in the top bar to launch acorn-core.")]
        ]
  let vitalsNodes : List Node := match proj.selectedFull with
    | some f =>
      let inv := [
        el .span (if f.wood == 0 then [kv .cls "off"] else []) [txt s!"wood {f.wood}"],
        el .span (if f.stone == 0 then [kv .cls "off"] else []) [txt s!"stone {f.stone}"],
        el .span (if f.food == 0 then [kv .cls "off"] else []) [txt s!"food {f.food}"],
        el .span (if f.gold == 0 then [kv .cls "off"] else []) [txt s!"gold {f.gold}"],
        el .span (if !f.axe then [kv .cls "off"] else []) [txt (if f.axe then "axe ✓" else "axe —")],
        el .span (if !f.boat then [kv .cls "off"] else []) [txt (if f.boat then "boat ✓" else "boat —")]
      ]
      [el .span [kv .title "energy"] [txt "⚡"],
       el .progress [kv .cls "energy-bar", kv .value (toString (min 100 f.energy)), kv .max "100"] [],
       el .span [kv .cls "inv"] inv]
    | none =>
      let msg := if proj.selectedIsEarlier then
          "vitals & inventory retained for newest frame only"
        else
          "energy — · inventory — (unavailable until first frame)"
      [el .span [kv .title "energy"] [txt "⚡"],
       el .span [kv .cls "inv"] [el .span [kv .cls "off"] [txt msg]]]
  let (skillLabel, skillCls, skillSub) := match proj.selectedFull, displaySummary with
    | some f, _ =>
      let skName := if f.summary.skill < f.skillNames.size then
        f.skillNames[f.summary.skill]?.getD "—"
        else "primitive"
      let skSub := if f.summary.skill < 3 then
        s!"elapsed {f.optionElapsed} · {f.summary.decisionSource}"
        else s!"{f.summary.decisionSource}"
      (skName, optionClass f.summary.skill, skSub)
    | none, some s =>
      let skName :=
        if s.skill < 3 then
          (latestFrame.bind (·.skillNames[s.skill]?)).getD s!"option {s.skill + 1}"
        else "primitive"
      let skSub := if s.explored then s!"{s.decisionSource} · explored" else s.decisionSource
      (skName, optionClass s.skill, skSub)
    | none, none => ("—", "v none", "no frame yet")
  let stagePanel := el .div [kv .id "stage"] [
    el .div [kv .id "hud-head", kv .cls "hudrow"] [
      el .div [kv .cls "hudbox", kv .id "hud-goal"] [
        el .div [kv .cls "lbl"] [txt hudGoalLbl],
        el .div [kv .cls "txt"] [txt hudGoalText],
        el .div [kv .cls "meta"] [txt hudGoalMeta]
      ],
      el .div [kv .cls "hudbox", kv .id "hud-time"] [
        el .div [kv .cls "lbl"] [txt s!"current world · {modeLabel}"],
        el .div [kv .cls "t"] [txt s!"{worldStat} · {hudTod}"],
        el .div [kv .cls "hint"] [txt "Resets when the world restarts"]
      ]
    ],
    el .div [kv .id "map-surface"] [mapSurfaceChild],
    el .div [kv .id "hud-foot", kv .cls "hudrow"] [
      el .div [kv .cls "hudbox", kv .id "hud-vitals"] vitalsNodes,
      el .div [kv .cls "hudbox", kv .id "hud-skill"] [
        el .div [kv .cls "lbl"] [txt (if proj.selectedIsEarlier then s!"option at frame #{curOneBased}" else "running option")],
        el .div [kv .cls skillCls] [txt skillLabel],
        el .div [kv .cls "sub2"] [txt skillSub]
      ]
    ]
  ]
  let stepHref (target : Nat) : String :=
    let bounded := if bufferedCount == 0 then 1 else max 1 (min bufferedCount target)
    { query with mode := .paused, frame := some bounded, stream := false }.href
  let liveHref := { query with mode := .live, frame := none }.href
  let pauseHref := { query with mode := .paused, frame := some curOneBased, stream := false }.href
  let transportSummary :=
    if bufferedCount == 0 then "0 buffered frames"
    else if proj.selectedIsEarlier then
      s!"Showing buffered frame {curOneBased} of {bufferedCount} ({bufferedCount - curOneBased} behind newest · {formatNatCommas observer.admittedCount} admitted) — summary fields reflect frame #{curOneBased}; full-frame panels are labelled newest frame or lifetime"
    else
      s!"Showing buffered frame {curOneBased} of {bufferedCount} ({formatNatCommas observer.admittedCount} admitted)"
  let transportPanel := el .div [kv .cls "panel"] [
    el .h2 [] [txt "Transport & zero-JS view controls"],
    el .div [kv .id "transport"] [
      el .a [kv .cls (if query.mode == .live then "btn livebtn active" else "btn livebtn"),
        kv .href liveHref] [txt "Live"],
      el .a [kv .cls (if query.mode == .paused then "btn active" else "btn"),
        kv .href pauseHref] [txt "Pause"],
      el .a [kv .cls "btn", kv .href (stepHref 1)] [txt "⏮"],
      el .a [kv .cls "btn", kv .href (stepHref (curOneBased - 10))] [txt "◀ -10"],
      el .a [kv .cls "btn", kv .href (stepHref (curOneBased - 1))] [txt "◀ -1"],
      el .a [kv .cls "btn", kv .href (stepHref (curOneBased + 1))] [txt "+1 ▶"],
      el .a [kv .cls "btn", kv .href (stepHref (curOneBased + 10))] [txt "+10 ▶"],
      el .a [kv .cls "btn", kv .href (stepHref (max 1 bufferedCount))] [txt "⏭"],
      el .form [kv .method "GET", kv .action "/", kv .cls "jump-form"] [
        vd .input [kv .type "hidden", kv .name "view", kv .value "paused"],
        whenNode (query.refresh != .auto)
          (vd .input [kv .type "hidden", kv .name "refresh", kv .value query.refresh.tag]),
        whenNode query.inside (vd .input [kv .type "hidden", kv .name "inside", kv .value "1"]),
        vd .input [kv .type "number", kv .name "frame", kv .cls "jump-input",
          kv .min "1", kv .max (toString (max 1 bufferedCount)),
          kv .value (toString curOneBased), kv .ariaLabel "Buffered frame index"],
        el .button [kv .type "submit", kv .cls "btn"] [txt "Jump"]
      ],
      el .span [kv .cls "legend"] [txt "Refresh:"],
      el .a [kv .cls (if query.refresh == .auto then "btn active" else "btn"),
        kv .href { query with refresh := .auto }.href] [txt "Auto"],
      el .a [kv .cls (if query.refresh == .sec1 then "btn active" else "btn"),
        kv .href { query with refresh := .sec1 }.href] [txt "1s"],
      el .a [kv .cls (if query.refresh == .sec2 then "btn active" else "btn"),
        kv .href { query with refresh := .sec2 }.href] [txt "2s"],
      el .a [kv .cls (if query.refresh == .sec5 then "btn active" else "btn"),
        kv .href { query with refresh := .sec5 }.href] [txt "5s"],
      el .a [kv .cls (if query.refresh == .off then "btn active" else "btn"),
        kv .href { query with refresh := .off }.href] [txt "Off"],
      el .a [kv .cls (if !query.stream then "btn active" else "btn"),
        kv .href { query with stream := false }.href] [txt "SVG Stage"],
      el .a [kv .cls (if query.stream then "btn active" else "btn"),
        kv .href { query with stream := true, mode := .live, frame := none }.href] [txt "Live Stream (BMP)"],
      el .a [kv .cls "btn", kv .href "/stage.bmp"] [txt "BMP Snapshot"]
    ],
    el .div [kv .cls "legend-row"] [
      el .span [kv .cls (if query.mode == .paused then "lag" else "lag ok")] [txt transportSummary],
      el .span [kv .cls "legend"] [
        txt (match refreshSecs with
          | some s =>
            if query.stream then s!"Live BMP stream · HTML auto-refresh: every {s}s"
            else s!"Auto-refresh: every {s}s (HTML meta refresh)"
          | none =>
            if query.stream then "Live BMP stream · HTML auto-refresh: off (as-of snapshot)"
            else "Auto-refresh: off")
      ]
    ]
  ]
  let ribbonPanel := el .div [kv .cls "panel"] [
    el .h2 [] [txt "Temporal abstraction — which option is running, and for how long"],
    el .div [kv .cls "lede"] [
      txt "Each band is one option the meta-controller committed to across the server's buffered replay window. Top ticks mark option starts; bottom ticks mark ends; violet lines mark goal changes."
    ],
    el .details [kv .cls "cite"] [
      el .summary [] [txt "sources"],
      el .div [kv .cls "body"] [
        txt "Sutton, Precup & Singh, AIJ 112 (1999) p. 17 (interruption compares Q",
        el .sup [] [txt "μ"], txt "(s", el .sub [] [txt "t"], txt ", o) to V",
        el .sup [] [txt "μ"], txt "(s)); Dabney, Ostrovski & Barreto, arXiv:2006.01782v1 §4.2 (exploratory runs)."
      ]
    ],
    renderRibbonSvg summaries (if query.mode == .paused then clampedIdx else none),
    el .div [kv .cls "legend-row"] [
      el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-opt1"] [], txt "option 1"],
      el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-opt2"] [], txt "option 2"],
      el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-opt3"] [], txt "option 3"],
      el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-goal"] [], txt "goal change"]
    ]
  ]
  let mapHistoryText := match snapshot.world with
    | some ⟨_, mem⟩ =>
      if snapshot.observation.mapPartial || mem.isIncomplete then
        "partial (observations may be missing around stops, restarts, or drops)"
      else
        "complete since start"
    | none =>
      if snapshot.observation.mapPartial then
        "unavailable (no retained map; history may be partial)"
      else match latestFrame with
        | some f =>
          if f.summary.side > mapSideCapacity then
            s!"unavailable (world side {formatNatCommas f.summary.side} exceeds {formatNatCommas mapSideCapacity} server map limit)"
          else
            "unavailable (no terrain observed yet)"
        | none => "unavailable (no terrain observed yet)"
  let worldSideText := match snapshot.world with
    | some ⟨key, _⟩ => s!"{key.side.val} × {key.side.val}"
    | none =>
      match latestFrame with
      | some f =>
        if f.summary.side > mapSideCapacity then s!"{f.summary.side} × {f.summary.side} (unretained)"
        else s!"{f.summary.side} × {f.summary.side}"
      | none => "—"
  let sensorEmptyCaption :=
    if proj.selectedIsEarlier then "Newest frame only" else "No sensor frame yet"
  let overviewEmptyCaption := match latestFrame with
    | some f =>
      if f.summary.side > mapSideCapacity then "Exceeds 4,096 map limit"
      else "No terrain map yet"
    | none => "No terrain map yet"
  let worldPanels := el .div [kv .id "world-panels"] [
    el .div [kv .cls "panel"] [
      el .h2 [] [txt (if proj.selectedIsEarlier then s!"What the agent sees · frame #{curOneBased} summary" else "What the agent sees (11 × 11 sensor)")],
      el .div [kv .cls "lede"] [txt (if proj.selectedIsEarlier then s!"Position, facing, and action reflect frame #{curOneBased}. The 11 × 11 sensor patch is retained for newest frame #{bufferedCount} only." else "Egocentric terrain, food (orange) and deer (brown) within the 11 × 11 sensor patch.")],
      kvRow "position" (match displaySummary with | some s => s!"({s.x}, {s.y})" | none => "—"),
      kvRow "facing" (match displaySummary with
        | some s => match s.facing with | 0 => "north" | 1 => "south" | 2 => "east" | _ => "west"
        | none => "—"),
      kvRow "last action" (match displaySummary with
        | some s => (latestFrame.bind (·.actionNames[s.action]?)).getD (toString s.action)
        | none => "—"),
      el .div [kv .cls "legend-row"] [
        el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-w0"] [], txt "water"],
        el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-w1"] [], txt "sand"],
        el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-w2"] [], txt "grass"],
        el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-w4"] [], txt "forest"],
        el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-w5"] [], txt "rock"],
        el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-w7"] [], txt "gold"]
      ],
      renderSensorSvg proj.selectedFull sensorEmptyCaption
    ],
    el .div [kv .cls "panel"] [
      el .h2 [] [txt "Big world overview"],
      el .div [kv .cls "lede"] [txt (if proj.selectedIsEarlier then s!"Retained run terrain memory (through newest frame #{bufferedCount}); white marker shows selected frame #{curOneBased} pose." else "Retained terrain memory across the world (persisted in explored.map).")],
      kvRow "explored" seenStat,
      kvRow "world side" worldSideText,
      kvRow "map history" mapHistoryText,
      kvRow "seed" (toString lifecycle.identityValue.seed),
      renderWorldOverviewSvg snapshot.world displaySummary proj.selectedFull overviewEmptyCaption
    ]
  ]
  let insideNodes : List Node :=
    let liveLit := liveness == .live && query.mode == .live && !proj.selectedIsEarlier
    let missionStrip :=
      let (fOn, sOn, oOn, mOn, pOn, fVal, sVal, oVal, mVal, pVal) := match latestFrame with
        | some f =>
          let fLive : Bool := liveLit && observer.retireChangedAt == some observer.admittedCount
          let sLive : Bool := liveLit && observer.subtaskChangedAt == some observer.admittedCount
          let oLive : Bool := liveLit && decide (f.summary.skill < 3)
          let mLive : Bool := liveLit && decide (f.summary.optionEndSkill < 3)
          let pLive : Bool := liveLit && observer.planningChangedAt == some observer.admittedCount
          (fLive, sLive, oLive, mLive, pLive,
           s!"{formatNatCommas f.imprintUnits} units · {formatNatCommas f.retireCount} retired",
           s!"{f.subtaskPolicy}",
           if f.summary.skill < 3 then f.skillNames[f.summary.skill]?.getD "active" else "primitive",
           s!"3 option models",
           s!"{formatNatCommas f.planningSteps} backups")
        | none => (false, false, false, false, false, "—", "—", "—", "—", "—")
      let agScoreStr := match observer.agreement with
        | some ag => ag.text.getD (formatPermilleScore ag.score ag.scale)
        | none => "—"
      let (gpScoreStr, gpTileCaption) := match observer.agreement with
        | some ag =>
          let disp := goalHeadlineDisplay ag.goalProgress ag.stopped
          (disp.value, disp.tileCaption)
        | none => ("—", "No curriculum snapshot")
      let plastStr := match displaySummary with
        | some s => s.aCtl.formatCompact 4
        | none => "—"
      let oakHeading := if proj.selectedIsEarlier then
          s!"OaK loop (FC-STOMP · newest frame #{bufferedCount})"
        else "OaK loop (FC-STOMP)"
      let plastCaption := if proj.selectedIsEarlier then
          s!"SwiftTD step size · frame #{curOneBased}"
        else "SwiftTD step size"
      el .div [kv .id "mission"] [
        el .div [kv .cls "panel thesis"] [
          el .div [kv .cls "q"] [txt "One continual learner in a big world."],
          el .p [] [txt "Acorn implements the Options and Knowledge (OaK) FC-STOMP loop in verified Lean, observed through a pure zero-JS server with strict CSP."],
          el .p [kv .cls "fine"] [txt "Read-only observer: zero client scripting, zero simulation shortcuts."]
        ],
        el .div [kv .cls "panel"] [
          el .h2 [] [txt oakHeading],
          el .div [kv .id "loop"] [
            el .div [kv .cls (if fOn then "node on" else "node")] [
              el .div [kv .cls "t"] [txt "1. Features"], el .div [kv .cls "v"] [txt fVal],
              el .div [kv .cls "c"] [txt "Imprinted & retired units"]
            ],
            el .div [kv .cls (if sOn then "node on" else "node")] [
              el .div [kv .cls "t"] [txt "2. Subtasks"], el .div [kv .cls "v"] [txt sVal],
              el .div [kv .cls "c"] [txt "Feature-attainment goals"]
            ],
            el .div [kv .cls (if oOn then "node on" else "node")] [
              el .div [kv .cls "t"] [txt "3. Options"], el .div [kv .cls "v"] [txt oVal],
              el .div [kv .cls "c"] [txt "Committed temporal skills"]
            ],
            el .div [kv .cls (if mOn then "node on" else "node")] [
              el .div [kv .cls "t"] [txt "4. Models"], el .div [kv .cls "v"] [txt mVal],
              el .div [kv .cls "c"] [txt "Reward, gamma & duration"]
            ],
            el .div [kv .cls (if pOn then "node on" else "node"), kv .id "n_planning"] [
              el .div [kv .cls "t"] [txt "5. Planning"], el .div [kv .cls "v"] [txt pVal],
              el .div [kv .cls "c"] [txt "Background Dyna backups"]
            ]
          ]
        ],
        el .div [kv .cls "panel"] [
          el .h2 [] [txt "Headline readouts"],
          el .div [kv .cls "tiles"] [
            el .div [kv .cls "tile"] [el .div [kv .cls "k"] [txt "Goal achievement"], el .div [kv .cls "v"] [txt gpScoreStr], el .div [kv .cls "d"] [txt gpTileCaption]],
            el .div [kv .cls "tile"] [el .div [kv .cls "k"] [txt "Agreement"], el .div [kv .cls "v"] [txt agScoreStr], el .div [kv .cls "d"] [txt "Process-local GVFs"]],
            el .div [kv .cls "tile"] [el .div [kv .cls "k"] [txt "Control α"], el .div [kv .cls "v"] [txt plastStr], el .div [kv .cls "d"] [txt plastCaption]],
            el .div [kv .cls "tile"] [el .div [kv .cls "k"] [txt "Frames"], el .div [kv .cls "v"] [txt (formatCompactNat observer.admittedCount)], el .div [kv .cls "d"] [txt "Admitted in run"]]
          ]
        ]
      ]
    let knowledgeCol :=
      match observer.agreement, latestFrame with
      | some ag, some f =>
        let agScoreText := ag.text.getD (formatPermilleScore ag.score ag.scale)
        let agStopTag := if ag.stopped then " · stopped" else ""
        let cards := (List.range 11).map fun idx =>
          let name := ag.demonNames[idx]?.getD s!"GVF {idx + 1}"
          let policy := ag.demonTargetPolicy[idx]?.getD "—"
          let status := ag.status[idx]?.getD "—"
          let sc := ag.channelText[idx]?.join.getD (formatPermilleScore (ag.channelScore[idx]?.join) ag.scale)
          let hasSc := (ag.channelScore[idx]?.join).isSome
          let settled := ag.count[idx]?.getD "0"
          let pend := ag.pending[idx]?.getD 0
          let cens := ag.censored[idx]?.getD "0"
          let pred := (f.demons[idx]?.getD .nonFinite).formatCompact 3
          let cum := (f.cums[idx]?.getD .nonFinite).formatCompact 3
          let ret := (f.settledReturn[idx]?.getD .nonFinite).formatCompact 3
          let err := (f.settledError[idx]?.getD .nonFinite).formatCompact 3
          el .div [kv .cls "agreement-card"] [
            el .h3 [] [txt name],
            el .strong (if hasSc then [kv .cls "has-score"] else []) [txt sc],
            el .p [] [txt s!"status: {status} · policy: {policy} · settled: {settled} · pending: {pend} · censored: {cens}"],
            el .p [] [txt s!"newest frame — pred: {pred} · cum: {cum} · return: {ret} · err: {err}"]
          ]
        el .div [kv .cls "panel"] [
          el .h2 [] [txt "Knowledge — predictive agreement & GVFs"],
          whenNode proj.selectedIsEarlier
            (el .div [kv .cls "scope-note"] [txt s!"Scope: process-local agreement snapshot and newest-frame (#{bufferedCount}) GVF/lifetime readouts (independent of paused frame #{curOneBased})."]),
          el .div [kv .cls "agreement-primary"] [
            el .strong (if ag.score.isSome then [kv .cls "has-score"] else []) [txt agScoreText],
            whenNode ag.score.isSome
              (el .progress [kv .value (toString (ag.score.getD 0)), kv .max (toString (max 1 ag.scale))] []),
            el .div [kv .cls "lede"] [txt s!"Clock {formatNatCommas ag.clock}{agStopTag} · stride {ag.settleStride} · source {(ag.sourceSha.take 12).toString} · build {(ag.buildSha.take 12).toString}"]
          ],
          renderAgreementHistorySvg ag,
          el .h3 [] [txt "Lifetime error (blue) & reward (green) · checkpoint-persistent"],
          renderLifetimeHistorySvg f,
          el .h3 [] [txt (if proj.selectedIsEarlier then s!"11 General Value Functions · process snapshot & newest frame #{bufferedCount}" else "11 General Value Functions")],
          el .div [kv .cls "agreement-channels"] cards
        ]
      | _, _ =>
        el .div [kv .cls "panel"] [
          el .h2 [] [txt "Knowledge — predictive agreement & GVFs"],
          el .div [kv .cls "lede"] [txt "No frames admitted yet."]
        ]
    let behaviourCol :=
      match latestFrame, displaySummary with
      | some f, some s =>
        let optRows := (List.range 3).map fun idx =>
          let nm := f.skillNames[idx]?.getD s!"Option {idx + 1}"
          let started := f.lifetimeOptionStarted[idx]?.getD 0
          let comp := f.lifetimeOptionCompleted[idx]?.getD 0
          let dur := f.lifetimeOptionDuration[idx]?.getD 0
          let meanDur := if comp > 0 then formatDecimal1 (dur * 10 / comp) else "—"
          let mRew := (f.optionModelRewards[idx]?.getD .nonFinite).formatCompact 3
          let mCont := (f.optionModelContinuations[idx]?.getD .nonFinite).formatCompact 3
          let mDur := (f.optionModelDurations[idx]?.getD .nonFinite).formatCompact 2
          el .tr [] [
            el .td [] [txt nm],
            el .td [] [txt s!"{formatNatCommas started}/{formatNatCommas comp}"],
            el .td [] [txt meanDur],
            el .td [] [txt mRew],
            el .td [] [txt mCont],
            el .td [] [txt mDur]
          ]
        let newestTag := if proj.selectedIsEarlier then s!" · newest frame #{bufferedCount}" else ""
        let rewardRows : List Node :=
          if proj.selectedIsEarlier then
            [kvRow s!"reward (frame #{curOneBased})" (s.reward.formatCompact 3) (!s.reward.isFinite),
             kvRow s!"reward rate (newest frame #{bufferedCount})" (f.rewardRate.formatCompact 4) (!f.rewardRate.isFinite)]
          else
            [kvRow "reward / rate" s!"{s.reward.formatCompact 3} / {f.rewardRate.formatCompact 4}" (!s.reward.isFinite || !f.rewardRate.isFinite)]
        el .div [kv .cls "panel"] (
          [el .h2 [] [txt "Behaviour — values, options & surprise"],
           whenNode proj.selectedIsEarlier
             (el .div [kv .cls "scope-note"] [txt s!"Decision source, ε, and reward reflect selected frame #{curOneBased}; reward rate, value bars, and option models reflect newest frame #{bufferedCount}."]),
           kvRow "decision source" s.decisionSource,
           kvRow "exploration (ε)" (s.eps.formatCompact 4) (!s.eps.isFinite)] ++
          rewardRows ++
          [kvRow "control criterion" (if f.controlCriterion == 0 then "average reward" else "discounted"),
           el .h3 [] [txt s!"Primitive actions (value & probability{newestTag})"],
           renderDivergingBarsSvg f.actionNames f.controlValues f.actionProbs "Primitive action values and probabilities",
           el .h3 [] [txt s!"Meta-controller (value & probability{newestTag})"],
           renderDivergingBarsSvg f.metaNames f.metaValues f.metaProbs "Meta-action values and probabilities",
           el .h3 [] [txt s!"Option models{newestTag} & lifetime execution"],
           el .table [kv .cls "data"] [
             el .thead [] [el .tr [] [
               el .th [] [txt "Option"], el .th [] [txt "Start/End"], el .th [] [txt "Mean dur"],
               el .th [] [txt "Model R"], el .th [] [txt "Model γ"], el .th [] [txt "Model d"]
             ]],
             el .tbody [] optRows
           ],
           el .h3 [] [txt "TD surprise across sampled run steps (independent of cursor)"],
           renderSurpriseSvg observer.samples.values]
        )
      | _, _ =>
        el .div [kv .cls "panel"] [
          el .h2 [] [txt "Behaviour — values, options & surprise"],
          el .div [kv .cls "lede"] [txt "No frames admitted yet."]
        ]
    let col3 :=
      match latestFrame, displaySummary with
      | some f, some s =>
        let famRows := (List.range 4).map fun idx =>
          let nm := f.goalFamilyNames[idx]?.getD s!"Family {idx}"
          let att := f.lifetimeGoalAttempts[idx]?.getD 0
          let suc := f.lifetimeGoalSuccesses[idx]?.getD 0
          let stp := f.lifetimeGoalSteps[idx]?.getD 0
          el .tr [] [
            el .td [] [txt nm],
            el .td [] [txt s!"{formatNatCommas suc}/{formatNatCommas att}"],
            el .td [] [txt (formatPercent1 suc att)],
            el .td [] [txt (if suc > 0 then formatNatCommas (stp / suc) else "—")]
          ]
        let headScope := if proj.selectedIsEarlier then s!" · newest frame #{bufferedCount}" else ""
        let aMetaStr := match s.aMeta with | some d => d.formatCompact 4 | none => "⚠ non-finite"
        let aOptStr := match s.aOpt with | some d => d.formatCompact 4 | none => "⚠ non-finite"
        el .div [kv .id "col3"] [
          el .div [kv .cls "panel"] [
            el .h2 [] [txt "Curriculum & cycle buckets"],
            el .div [kv .cls "scope-note"] [txt (if proj.selectedIsEarlier then s!"Scope: checkpoint-persistent lifetime totals (as of newest frame #{bufferedCount})." else "Scope: checkpoint-persistent lifetime totals.")],
            el .table [kv .cls "data"] [
              el .thead [] [el .tr [] [
                el .th [] [txt "Family"], el .th [] [txt "Solved"], el .th [] [txt "Rate"], el .th [] [txt "Mean steps"]
              ]],
              el .tbody [] famRows
            ],
            el .h3 [] [txt "Cycle buckets (solved/attempts)"],
            renderCycleBucketTable f
          ],
          el .div [kv .cls "panel"] [
            el .h2 [] [txt "Plasticity — SwiftTD step sizes"],
            el .div [kv .cls "scope-note"] [txt (if proj.selectedIsEarlier then s!"Curve: sampled intake history (independent of cursor). Family means below reflect frame #{curOneBased}; per-head tables reflect newest frame #{bufferedCount}." else "Curve: sampled intake history (independent of cursor).")],
            renderPlasticitySvg observer.samples.values,
            el .div [kv .cls "legend-row"] [
              el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-dem"] [], txt "demons"],
              el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-ctl"] [], txt "control"],
              el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-met"] [], txt "meta"],
              el .span [kv .cls "legend"] [el .span [kv .cls "swatch sw-opt"] [], txt "options"]
            ],
            kvRow (if proj.selectedIsEarlier then s!"frame #{curOneBased} α (dem / ctl)" else "α (dem / ctl)")
              s!"{s.aDem.formatCompact 4} / {s.aCtl.formatCompact 4}" (!s.aDem.isFinite || !s.aCtl.isFinite),
            kvRow (if proj.selectedIsEarlier then s!"frame #{curOneBased} α (meta / opt)" else "α (meta / opt)")
              s!"{aMetaStr} / {aOptStr}" (s.aMeta.isNone || s.aOpt.isNone),
            learnerDetailNode s!"Control heads{headScope}" f.alphaControl f.creditControl,
            learnerDetailNode s!"Meta heads{headScope}" f.alphaMeta f.creditMeta,
            learnerDetailNode s!"Option heads{headScope}" f.alphaOptions f.creditOptions,
            learnerDetailNode s!"Demon heads{headScope}" f.alphaDemons f.creditDemons,
            learnerDetailNode s!"Model heads{headScope}" f.alphaModels f.creditModels
          ],
          el .div [kv .cls "panel"] [
            el .h2 [] [txt "Resources & telemetry health"],
            whenNode proj.selectedIsEarlier
              (el .div [kv .cls "scope-note"] [txt s!"Update/env latencies reflect selected frame #{curOneBased}; remaining figures are newest-frame process observations."]),
            kvRow "update / env" s!"{formatNatCommas s.updateUs} µs / {formatNatCommas s.environmentUs} µs",
            kvRow "process uptime" (formatDurationMs f.processUptimeMs),
            kvRow "core RSS" (match f.coreRssBytes with | some b => formatBytes b | none => "—"),
            kvRow "checkpoint size" (match f.checkpointBytes with | some b => formatBytes b | none => "—"),
            kvRow "checkpoint write" (match f.checkpointWriteUs with | some u => s!"{formatNatCommas u} µs" | none => "—"),
            kvRow "checkpoint failures" (formatNatCommas f.checkpointFailures) (f.checkpointFailures > 0),
            kvRow "core refusals / drops" s!"{formatNatCommas f.telemetryRefusals} / {formatNatCommas f.telemetryDrops}",
            kvRow "server refused / non-finite" s!"{formatNatCommas observer.refusedCount} / {formatNatCommas observer.nonFiniteCount}" (observer.refusedCount > 0 || observer.nonFiniteCount > 0),
            kvRow "weight space / tilings" s!"{formatNatCommas f.weightSpace} / {f.nTilings}",
            kvRow "audit digest" f.auditDigest
          ]
        ]
      | _, _ =>
        el .div [kv .id "col3"] [
          el .div [kv .cls "panel"] [
            el .h2 [] [txt "Resources & process health"],
            kvRow "run id" (runHex lifecycle.identityValue.run),
            kvRow "agent epoch" (toString lifecycle.identityValue.agentEpoch),
            kvRow "seed" (toString lifecycle.identityValue.seed),
            kvRow "lifecycle" label.state,
            kvRow "server refused / non-finite" s!"{formatNatCommas observer.refusedCount} / {formatNatCommas observer.nonFiniteCount}"
          ]
        ]
    [missionStrip, el .div [kv .id "bottom"] [knowledgeCol, behaviourCol, col3]]
  let researchAttrs := [kv .id "research", kv .cls "research-details"] ++
    (if query.inside then [flg .openAttr] else [])
  let researchDetails := el .details researchAttrs (
    [el .summary [] [txt "Explore what's happening inside — OaK loop, predictive agreement, behaviour, curriculum, plasticity & resources"]] ++
    insideNodes
  )
  {
    lang := "en"
    head := headNodes
    body := [
      topBar,
      noticeNode,
      lifecycleDiagnosticNode,
      welcomeSection,
      el .div [kv .id "main"] [
        el .div [kv .id "left"] [stagePanel, ribbonPanel, transportPanel],
        el .div [kv .id "right"] [renderGoalSidebar observer.agreement proj.selectedIsEarlier]
      ],
      worldPanels,
      researchDetails
    ]
  }

theorem renderViewerPage_no_script (snapshot : BroadcastSnapshot) (query : ViewQuery)
    (token : String) (notice : Option ControlNotice) (nowMonoMs : Nat) :
    ¬ Html.ContainsScriptTag (renderViewerPage snapshot query token notice nowMonoMs).render.toList :=
  Html.Document.render_no_script _

end Acorn.Host.Viewer
