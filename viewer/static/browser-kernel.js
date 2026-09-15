function observerFrameStore(CAP,N_DEM,N_CTL,N_META,N_TILE,N_SKILL,N_OPTION_END,N_GOAL_FAMILY){return {
  worldStep:new Float64Array(CAP),
  lifetimeStep:new Float64Array(CAP),
  agentEpoch:new Float64Array(CAP),
  origin:new Float64Array(CAP),
  x:new Float64Array(CAP),
  y:new Float64Array(CAP),
  facing:new Float64Array(CAP),
  action:new Float64Array(CAP),
  skill:new Float64Array(CAP),
  ev:new Float64Array(CAP),
  flags:new Float64Array(CAP),
  goal:new Float64Array(CAP),
  attempt:new Float64Array(CAP),
  tier:new Float64Array(CAP),
  cycle:new Float64Array(CAP),
  goalCount:new Float64Array(CAP),
  attemptCap:new Float64Array(CAP),
  energy:new Float64Array(CAP),
  wood:new Float64Array(CAP),
  stone:new Float64Array(CAP),
  food:new Float64Array(CAP),
  gold:new Float64Array(CAP),
  reward:new Float64Array(CAP),
  eps:new Float64Array(CAP),
  alpha:new Float64Array(CAP),
  rewardRate:new Float64Array(CAP),
  criterion:new Float64Array(CAP),
  aCtl:new Float64Array(CAP),
  aDem:new Float64Array(CAP),
  updateUs:new Float64Array(CAP),
  environmentUs:new Float64Array(CAP),
  gkind:new Float64Array(CAP),
  gitem:new Float64Array(CAP),
  gx:new Float64Array(CAP),
  gy:new Float64Array(CAP),
  gn:new Float64Array(CAP),
  planningSteps:new Float64Array(CAP),
  retireCount:new Float64Array(CAP),
  retireStep:new Float64Array(CAP),
  retireUnit:new Float64Array(CAP),
  decisionSource:new Float64Array(CAP),
  explored:new Float64Array(CAP),
  metaAction:new Float64Array(CAP),
  optStart:new Float64Array(CAP),
  optEnd:new Float64Array(CAP),
  optEndReason:new Float64Array(CAP),
  optEndDuration:new Float64Array(CAP),
  optElapsed:new Float64Array(CAP),
  lifeRewardSum:new Float64Array(CAP),
  lifeRewardCount:new Float64Array(CAP),
  lifeErrorSum:new Float64Array(CAP),
  lifeErrorCount:new Float64Array(CAP),
  runStart:new Float64Array(CAP),
  dem:new Float64Array(CAP*N_DEM),
  cum:new Float64Array(CAP*N_DEM),
  alphaDemons:new Float64Array(CAP*N_DEM),
  creditDemons:new Float64Array(CAP*N_DEM),
  lifeErrorCountD:new Float64Array(CAP*N_DEM),
  settledReturn:new Float64Array(CAP*N_DEM),
  settledError:new Float64Array(CAP*N_DEM),
  ctl:new Float64Array(CAP*N_CTL),
  actProb:new Float64Array(CAP*N_CTL),
  alphaControl:new Float64Array(CAP*N_CTL),
  creditControl:new Float64Array(CAP*N_CTL),
  met:new Float64Array(CAP*N_META),
  metaProb:new Float64Array(CAP*N_META),
  alphaMeta:new Float64Array(CAP*N_META),
  creditMeta:new Float64Array(CAP*N_META),
  optModRew:new Float64Array(CAP*N_SKILL),
  optModCont:new Float64Array(CAP*N_SKILL),
  optModDuration:new Float64Array(CAP*N_SKILL),
  planningErrors:new Float64Array(CAP*N_SKILL),
  subtaskUnit:new Float64Array(CAP*N_SKILL),
  subtaskBonus:new Float64Array(CAP*N_SKILL),
  lifeOptStarted:new Float64Array(CAP*N_SKILL),
  lifeOptCompleted:new Float64Array(CAP*N_SKILL),
  lifeOptDuration:new Float64Array(CAP*N_SKILL),
  alphaOptions:new Float64Array(CAP*N_CTL*N_SKILL),
  creditOptions:new Float64Array(CAP*N_CTL*N_SKILL),
  alphaModels:new Float64Array(CAP*3*N_SKILL),
  creditModels:new Float64Array(CAP*3*N_SKILL),
  lifeOptEndReasons:new Float64Array(CAP*N_SKILL*N_OPTION_END),
  lifeGoalAttempts:new Float64Array(CAP*N_GOAL_FAMILY),
  lifeGoalSuccesses:new Float64Array(CAP*N_GOAL_FAMILY),
  lifeGoalSteps:new Float64Array(CAP*N_GOAL_FAMILY),
  lifeRewardFamilySum:new Float64Array(CAP*N_GOAL_FAMILY),
  lifeRewardFamilyCount:new Float64Array(CAP*N_GOAL_FAMILY),
  cycleAttempts:new Float64Array(CAP*N_GOAL_FAMILY),
  cycleSuccesses:new Float64Array(CAP*N_GOAL_FAMILY),
  cycleSteps:new Float64Array(CAP*N_GOAL_FAMILY),
  runId:new Array(CAP),
  tiles:new Uint8Array(CAP*N_TILE), extra:new Uint8Array(CAP*N_TILE),
};}
function observerStore(id, f) {
  const i = slot(id);
  S.worldStep[i]=f.world_step; S.lifetimeStep[i]=f.lifetime_step;
  S.runId[i]=f.runId; S.agentEpoch[i]=f.agent_epoch;
  S.origin[i] = f.origin === "resumed" ? 1 : f.origin === "cleared" ? 2 : 0;
  S.x[i]=f.x; S.y[i]=f.y; S.facing[i]=f.facing; S.action[i]=f.action;
  S.skill[i]=f.skill; S.ev[i]=f.ev; S.goal[i]=f.goal; S.attempt[i]=f.attempt;
  S.tier[i]=f.tier; S.cycle[i]=f.cycle; S.goalCount[i]=f.goal_count;
  S.attemptCap[i]=f.attempt_cap; S.energy[i]=f.energy; S.wood[i]=f.wood;
  S.stone[i]=f.stone; S.food[i]=f.food;
  S.gold[i]=f.gold; S.reward[i]=f.reward; S.eps[i]=f.eps;
  S.rewardRate[i]=f.reward_rate; S.criterion[i]=f.control_criterion;
  S.alpha[i]=f.mean_alpha; S.aCtl[i]=f.a_ctl; S.aDem[i]=f.a_dem;
  S.updateUs[i]=f.update_us; S.environmentUs[i]=f.environment_us;
  S.gkind[i]=f.gkind; S.gitem[i]=f.gitem;
  S.gx[i]=f.gx; S.gy[i]=f.gy; S.gn[i]=f.gn;
  S.flags[i] = (f.axe?1:0)|(f.boat?2:0)|(f.done?4:0)|(f.end?8:0);
  S.dem.set(f.dem, i*N_DEM);
  S.cum.set(f.cum, i*N_DEM);
  S.ctl.set(f.ctl, i*N_CTL);
  S.met.set(f.met, i*N_META);
  S.actProb.set(f.actProb, i*N_CTL); S.metaProb.set(f.metaProb, i*N_META);
  S.decisionSource[i] = ["primitive","exploration_start","exploration_continuation","option"].indexOf(f.decisionSource);
  S.explored[i] = f.explored ? 1 : 0; S.metaAction[i]=f.meta_action;
  S.optStart[i]=f.option_start; S.optEnd[i]=f.option_end_skill;
  S.optEndReason[i]=f.option_end_reason; S.optEndDuration[i]=f.option_end_duration;
  S.optElapsed[i]=f.option_elapsed;
  S.optModRew.set(f.optModRew, i*N_SKILL);
  S.optModCont.set(f.optModCont, i*N_SKILL);
  S.optModDuration.set(f.optModDuration, i*N_SKILL);
  S.planningSteps[i]=f.planning_steps;
  S.planningErrors.set(f.planningErrors, i*N_SKILL);
  S.subtaskUnit.set(f.subtaskUnit, i*N_SKILL); S.subtaskBonus.set(f.subtaskBonus, i*N_SKILL);
  S.retireCount[i]=f.retire_count; S.retireStep[i]=f.retire_step; S.retireUnit[i]=f.retire_unit;
  S.alphaControl.set(f.alphaControl,i*N_CTL); S.alphaMeta.set(f.alphaMeta,i*N_META);
  S.alphaOptions.set(f.alphaOptions,i*N_CTL*N_SKILL); S.alphaDemons.set(f.alphaDemons,i*N_DEM);
  S.alphaModels.set(f.alphaModels,i*3*N_SKILL);
  S.creditControl.set(f.creditControl,i*N_CTL); S.creditMeta.set(f.creditMeta,i*N_META);
  S.creditOptions.set(f.creditOptions,i*N_CTL*N_SKILL); S.creditDemons.set(f.creditDemons,i*N_DEM);
  S.creditModels.set(f.creditModels,i*3*N_SKILL);
  S.lifeRewardSum[i]=f.lifetime_reward_sum; S.lifeRewardCount[i]=f.lifetime_reward_count;
  S.lifeErrorSum[i]=observerSum(f.lifeErrorSum);
  S.lifeErrorCount[i]=observerSum(f.lifeErrorCount);
  S.lifeErrorCountD.set(f.lifeErrorCount,i*N_DEM); S.settledReturn.set(f.settledReturn,i*N_DEM);
  S.settledError.set(f.settledError,i*N_DEM);
  S.lifeOptStarted.set(f.lifeOptStarted,i*N_SKILL);
  S.lifeOptCompleted.set(f.lifeOptCompleted,i*N_SKILL);
  S.lifeOptDuration.set(f.lifeOptDuration,i*N_SKILL);
  S.lifeOptEndReasons.set(f.lifeOptEndReasons,i*N_SKILL*N_OPTION_END);
  S.lifeGoalAttempts.set(f.lifeGoalAttempts,i*N_GOAL_FAMILY);
  S.lifeGoalSuccesses.set(f.lifeGoalSuccesses,i*N_GOAL_FAMILY);
  S.lifeGoalSteps.set(f.lifeGoalSteps,i*N_GOAL_FAMILY);
  S.lifeRewardFamilySum.set(f.lifeRewardFamilySum,i*N_GOAL_FAMILY);
  S.lifeRewardFamilyCount.set(f.lifeRewardFamilyCount,i*N_GOAL_FAMILY);
  const cb=cycleBucket(f.cycle);
  for(let family=0;family<N_GOAL_FAMILY;family++){
    const src=family*CYCLE_BINS+cb,dst=i*N_GOAL_FAMILY+family;
    S.cycleAttempts[dst]=f.lifeCycleAttempts[src];
    S.cycleSuccesses[dst]=f.lifeCycleSuccesses[src];
    S.cycleSteps[dst]=f.lifeCycleSteps[src];
  }
  S.tiles.set(f.tiles, i*N_TILE);
  S.extra.set(f.extra, i*N_TILE);
}
const ObserverMath=Object.freeze({
sum:(p,rows)=>{const a=rows.reduce((a,x)=>[(a[0]+x[0])],[(0e-1074)]);return a[0];},
mean:(p,rows)=>{const a=rows.reduce((a,x)=>[(a[0]+x[0]),(a[1]+(10000000000000000000000000000000000000000000000000000e-52))],[(0e-1074),(0e-1074)]);return (((0e-1074)<a[1])?(a[0]/a[1]):NaN);},
meanAbsolute:(p,rows)=>{const a=rows.reduce((a,x)=>[(a[0]+Math.abs(x[0])),(a[1]+(10000000000000000000000000000000000000000000000000000e-52))],[(0e-1074),(0e-1074)]);return (((0e-1074)<a[1])?(a[0]/a[1]):NaN);},
countEqual:(p,rows)=>{const a=rows.reduce((a,x)=>[((p[0]===x[0])?(a[0]+(10000000000000000000000000000000000000000000000000000e-52)):a[0])],[(0e-1074)]);return a[0];},
ratio:(...p)=>(p[0]/p[1]),
meanPositive:(p,rows)=>{const a=rows.reduce((a,x)=>[(Number.isFinite(x[0])?(((0e-1074)<x[0])?(a[0]+x[0]):a[0]):NaN),(Number.isFinite(x[0])?(((0e-1074)<x[0])?(a[1]+(10000000000000000000000000000000000000000000000000000e-52)):a[1]):(a[1]+(10000000000000000000000000000000000000000000000000000e-52)))],[(0e-1074),(0e-1074)]);return (((0e-1074)<a[1])?(a[0]/a[1]):(0e-1074));},
finiteReturn:(p,rows)=>{const a=rows.reduce((a,x)=>[(a[0]+(a[1]*x[0])),(a[1]*p[0])],[(0e-1074),(10000000000000000000000000000000000000000000000000000e-52)]);return a[0];},
tdSurprise:(p,rows)=>{const a=rows.reduce((a,x)=>[(a[0]+Math.abs(((x[0]+(x[1]*x[2]))-x[3]))),(a[1]+(10000000000000000000000000000000000000000000000000000e-52))],[(0e-1074),(0e-1074)]);return (((0e-1074)<a[1])?(a[0]/a[1]):NaN);},
pairedLatency:(p,rows)=>{const a=rows.reduce((a,x)=>[(Number.isFinite(x[0])?(Number.isFinite(x[1])?(a[0]+x[0]):a[0]):a[0]),(Number.isFinite(x[0])?(Number.isFinite(x[1])?(a[1]+(10000000000000000000000000000000000000000000000000000e-52)):a[1]):a[1])],[(0e-1074),(0e-1074)]);return (((0e-1074)<a[1])?(a[0]/a[1]):NaN);},
normalizedError:(...p)=>(Math.abs((p[0]-p[1]))/((10000000000000000000000000000000000000000000000000000e-52)/((10000000000000000000000000000000000000000000000000000e-52)-p[2]))),
horizon:(...p)=>Math.min((6000000000000000000000000000000000000000000000e-43),Math.max((80000000000000000000000000000000000000000000000000e-49),Math.ceil((Math.log((1000000000000000020816681711721685132943093776702880859375e-59))/Math.log(p[0]))))),
relativeChange:(...p)=>(((99999999999999997988664762925561536725284350612952266601496376097202301025390625e-92)<Math.abs(p[1]))?((p[0]-p[1])/Math.abs(p[1])):((p[0]===p[1])?(0e-1074):Infinity)),
trend:(...p)=>(Number.isFinite(p[0])?(Number.isFinite(p[1])?((Math.abs((((99999999999999997988664762925561536725284350612952266601496376097202301025390625e-92)<Math.abs(p[1]))?((p[0]-p[1])/Math.abs(p[1])):((p[0]===p[1])?(0e-1074):Infinity)))<(50000000000000002775557561562891351059079170227050781250e-57))?(0e-1074):((p[1]<p[0])?(10000000000000000000000000000000000000000000000000000e-52):(-10000000000000000000000000000000000000000000000000000e-52))):NaN):NaN),
filling:(...p)=>((p[0]<(p[1]/(80000000000000000000000000000000000000000000000000e-49)))?(10000000000000000000000000000000000000000000000000000e-52):(0e-1074)),
enoughSamples:(...p)=>((p[0]<(30000000000000000000000000000000000000000000000000e-48))?(0e-1074):(10000000000000000000000000000000000000000000000000000e-52))
});
function observerGoalItemLabel(code){return ({0:"—",1:"Wood",2:"Stone",3:"Food",4:"Gold",11:"Axe",12:"Boat"})[code]??'—';}
function observerGoalText(gkind,gitem,gx,gy,gn){switch(gkind){case 0:return '—';case 1:return 'Go to the gold target ('+gx+', '+gy+')';case 2:return 'Hold '+gn+' '+observerGoalItemLabel(gitem);case 3:return 'Own '+observerGoalItemLabel(gitem);case 4:return 'Continue for '+gn+' world steps in this attempt';default:return '—';}}
function observerAdmission(f){
if(!f||typeof f!=='object'||Array.isArray(f))return {why:'malformed',key:'frame'};
if(!Object.hasOwn(f,"schema_version"))return {why:'missingField',key:"schema_version"};
if(!(Number.isSafeInteger(f["schema_version"])&&f["schema_version"]>=0))return {why:'malformed',key:"schema_version"};
if(!Object.hasOwn(f,"source_sha256"))return {why:'missingField',key:"source_sha256"};
if(!(typeof f["source_sha256"]==='string'))return {why:'malformed',key:"source_sha256"};
if(!Object.hasOwn(f,"build_sha256"))return {why:'missingField',key:"build_sha256"};
if(!(typeof f["build_sha256"]==='string'))return {why:'malformed',key:"build_sha256"};
if(!Object.hasOwn(f,"audit_digest"))return {why:'missingField',key:"audit_digest"};
if(!(typeof f["audit_digest"]==='string'))return {why:'malformed',key:"audit_digest"};
if(!Object.hasOwn(f,"run_id"))return {why:'missingField',key:"run_id"};
if(!(typeof f["run_id"]==='string'))return {why:'malformed',key:"run_id"};
if(!Object.hasOwn(f,"agent_epoch"))return {why:'missingField',key:"agent_epoch"};
if(!(Number.isSafeInteger(f["agent_epoch"])&&f["agent_epoch"]>=0))return {why:'malformed',key:"agent_epoch"};
if(!Object.hasOwn(f,"origin"))return {why:'missingField',key:"origin"};
if(!(typeof f["origin"]==='string'))return {why:'malformed',key:"origin"};
if(!Object.hasOwn(f,"timestamp_ms"))return {why:'missingField',key:"timestamp_ms"};
if(!(Number.isSafeInteger(f["timestamp_ms"])&&f["timestamp_ms"]>=0))return {why:'malformed',key:"timestamp_ms"};
if(!Object.hasOwn(f,"update_us"))return {why:'missingField',key:"update_us"};
if(!(Number.isSafeInteger(f["update_us"])&&f["update_us"]>=0))return {why:'malformed',key:"update_us"};
if(!Object.hasOwn(f,"environment_us"))return {why:'missingField',key:"environment_us"};
if(!(Number.isSafeInteger(f["environment_us"])&&f["environment_us"]>=0))return {why:'malformed',key:"environment_us"};
if(!Object.hasOwn(f,"process_uptime_ms"))return {why:'missingField',key:"process_uptime_ms"};
if(!(Number.isSafeInteger(f["process_uptime_ms"])&&f["process_uptime_ms"]>=0))return {why:'malformed',key:"process_uptime_ms"};
if(!Object.hasOwn(f,"process_started_ms"))return {why:'missingField',key:"process_started_ms"};
if(!(Number.isSafeInteger(f["process_started_ms"])&&f["process_started_ms"]>=0))return {why:'malformed',key:"process_started_ms"};
if(!Object.hasOwn(f,"core_rss_bytes"))return {why:'missingField',key:"core_rss_bytes"};
if(!(f["core_rss_bytes"]===null||(Number.isSafeInteger(f["core_rss_bytes"])&&f["core_rss_bytes"]>=0)))return {why:'malformed',key:"core_rss_bytes"};
if(!Object.hasOwn(f,"checkpoint_bytes"))return {why:'missingField',key:"checkpoint_bytes"};
if(!(f["checkpoint_bytes"]===null||(Number.isSafeInteger(f["checkpoint_bytes"])&&f["checkpoint_bytes"]>=0)))return {why:'malformed',key:"checkpoint_bytes"};
if(!Object.hasOwn(f,"checkpoint_write_us"))return {why:'missingField',key:"checkpoint_write_us"};
if(!(f["checkpoint_write_us"]===null||(Number.isSafeInteger(f["checkpoint_write_us"])&&f["checkpoint_write_us"]>=0)))return {why:'malformed',key:"checkpoint_write_us"};
if(!Object.hasOwn(f,"checkpoint_failures"))return {why:'missingField',key:"checkpoint_failures"};
if(!(Number.isSafeInteger(f["checkpoint_failures"])&&f["checkpoint_failures"]>=0))return {why:'malformed',key:"checkpoint_failures"};
if(!Object.hasOwn(f,"telemetry_refusals"))return {why:'missingField',key:"telemetry_refusals"};
if(!(Number.isSafeInteger(f["telemetry_refusals"])&&f["telemetry_refusals"]>=0))return {why:'malformed',key:"telemetry_refusals"};
if(!Object.hasOwn(f,"telemetry_drops"))return {why:'missingField',key:"telemetry_drops"};
if(!(Number.isSafeInteger(f["telemetry_drops"])&&f["telemetry_drops"]>=0))return {why:'malformed',key:"telemetry_drops"};
if(!Object.hasOwn(f,"goal_count"))return {why:'missingField',key:"goal_count"};
if(!(Number.isSafeInteger(f["goal_count"])&&f["goal_count"]>=0))return {why:'malformed',key:"goal_count"};
if(!Object.hasOwn(f,"attempt_cap"))return {why:'missingField',key:"attempt_cap"};
if(!(Number.isSafeInteger(f["attempt_cap"])&&f["attempt_cap"]>=0))return {why:'malformed',key:"attempt_cap"};
if(!Object.hasOwn(f,"step_cap"))return {why:'missingField',key:"step_cap"};
if(!(Number.isSafeInteger(f["step_cap"])&&f["step_cap"]>=0))return {why:'malformed',key:"step_cap"};
if(!Object.hasOwn(f,"cycle_cap"))return {why:'missingField',key:"cycle_cap"};
if(!(Number.isSafeInteger(f["cycle_cap"])&&f["cycle_cap"]>=0))return {why:'malformed',key:"cycle_cap"};
if(!Object.hasOwn(f,"goal_progress_invalid"))return {why:'missingField',key:"goal_progress_invalid"};
if(!(typeof f["goal_progress_invalid"]==='boolean'))return {why:'malformed',key:"goal_progress_invalid"};
if(!Object.hasOwn(f,"goal_progress_cycle"))return {why:'missingField',key:"goal_progress_cycle"};
if(!(Number.isSafeInteger(f["goal_progress_cycle"])&&f["goal_progress_cycle"]>=0))return {why:'malformed',key:"goal_progress_cycle"};
if(!Object.hasOwn(f,"goal_progress_resolved"))return {why:'missingField',key:"goal_progress_resolved"};
if(!(Number.isSafeInteger(f["goal_progress_resolved"])&&f["goal_progress_resolved"]>=0))return {why:'malformed',key:"goal_progress_resolved"};
if(!Object.hasOwn(f,"goal_progress_attempt"))return {why:'missingField',key:"goal_progress_attempt"};
if(!(Number.isSafeInteger(f["goal_progress_attempt"])&&f["goal_progress_attempt"]>=0))return {why:'malformed',key:"goal_progress_attempt"};
if(!Object.hasOwn(f,"goal_progress_achieved"))return {why:'missingField',key:"goal_progress_achieved"};
if(!(Number.isSafeInteger(f["goal_progress_achieved"])&&f["goal_progress_achieved"]>=0))return {why:'malformed',key:"goal_progress_achieved"};
if(!Object.hasOwn(f,"goal_progress_completed_cycle"))return {why:'missingField',key:"goal_progress_completed_cycle"};
if(!(f["goal_progress_completed_cycle"]===null||(Number.isSafeInteger(f["goal_progress_completed_cycle"])&&f["goal_progress_completed_cycle"]>=0)))return {why:'malformed',key:"goal_progress_completed_cycle"};
if(!Object.hasOwn(f,"goal_progress_completed_achieved"))return {why:'missingField',key:"goal_progress_completed_achieved"};
if(!(f["goal_progress_completed_achieved"]===null||(Number.isSafeInteger(f["goal_progress_completed_achieved"])&&f["goal_progress_completed_achieved"]>=0)))return {why:'malformed',key:"goal_progress_completed_achieved"};
if(!Object.hasOwn(f,"goal_progress_score"))return {why:'missingField',key:"goal_progress_score"};
if(!(f["goal_progress_score"]===null||(Number.isSafeInteger(f["goal_progress_score"])&&f["goal_progress_score"]>=0)))return {why:'malformed',key:"goal_progress_score"};
if(!Object.hasOwn(f,"curriculum_names"))return {why:'missingField',key:"curriculum_names"};
if(!(Array.isArray(f["curriculum_names"])&&f["curriculum_names"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"curriculum_names"};
if(!Object.hasOwn(f,"curriculum_failed_attempts"))return {why:'missingField',key:"curriculum_failed_attempts"};
if(!(Array.isArray(f["curriculum_failed_attempts"])&&f["curriculum_failed_attempts"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"curriculum_failed_attempts"};
if(!Object.hasOwn(f,"curriculum_success_steps"))return {why:'missingField',key:"curriculum_success_steps"};
if(!(Array.isArray(f["curriculum_success_steps"])&&f["curriculum_success_steps"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"curriculum_success_steps"};
if(!Object.hasOwn(f,"world_step"))return {why:'missingField',key:"world_step"};
if(!(Number.isSafeInteger(f["world_step"])&&f["world_step"]>=0))return {why:'malformed',key:"world_step"};
if(!Object.hasOwn(f,"seed"))return {why:'missingField',key:"seed"};
if(!(Number.isSafeInteger(f["seed"])&&f["seed"]>=0))return {why:'malformed',key:"seed"};
if(!Object.hasOwn(f,"side"))return {why:'missingField',key:"side"};
if(!(Number.isSafeInteger(f["side"])&&f["side"]>=0))return {why:'malformed',key:"side"};
if(!Object.hasOwn(f,"day_length"))return {why:'missingField',key:"day_length"};
if(!(Number.isSafeInteger(f["day_length"])&&f["day_length"]>=0))return {why:'malformed',key:"day_length"};
if(!Object.hasOwn(f,"regrow"))return {why:'missingField',key:"regrow"};
if(!(Number.isSafeInteger(f["regrow"])&&f["regrow"]>=0))return {why:'malformed',key:"regrow"};
if(!Object.hasOwn(f,"food_interval"))return {why:'missingField',key:"food_interval"};
if(!(Number.isSafeInteger(f["food_interval"])&&f["food_interval"]>=0))return {why:'malformed',key:"food_interval"};
if(!Object.hasOwn(f,"food_cap"))return {why:'missingField',key:"food_cap"};
if(!(Number.isSafeInteger(f["food_cap"])&&f["food_cap"]>=0))return {why:'malformed',key:"food_cap"};
if(!Object.hasOwn(f,"deer_cap"))return {why:'missingField',key:"deer_cap"};
if(!(Number.isSafeInteger(f["deer_cap"])&&f["deer_cap"]>=0))return {why:'malformed',key:"deer_cap"};
if(!Object.hasOwn(f,"x"))return {why:'missingField',key:"x"};
if(!Number.isSafeInteger(f["x"]))return {why:'malformed',key:"x"};
if(!Object.hasOwn(f,"y"))return {why:'missingField',key:"y"};
if(!Number.isSafeInteger(f["y"]))return {why:'malformed',key:"y"};
if(!Object.hasOwn(f,"facing"))return {why:'missingField',key:"facing"};
if(!(Number.isSafeInteger(f["facing"])&&f["facing"]>=0))return {why:'malformed',key:"facing"};
if(!Object.hasOwn(f,"energy"))return {why:'missingField',key:"energy"};
if(!(Number.isSafeInteger(f["energy"])&&f["energy"]>=0))return {why:'malformed',key:"energy"};
if(!Object.hasOwn(f,"wood"))return {why:'missingField',key:"wood"};
if(!(Number.isSafeInteger(f["wood"])&&f["wood"]>=0))return {why:'malformed',key:"wood"};
if(!Object.hasOwn(f,"stone"))return {why:'missingField',key:"stone"};
if(!(Number.isSafeInteger(f["stone"])&&f["stone"]>=0))return {why:'malformed',key:"stone"};
if(!Object.hasOwn(f,"food"))return {why:'missingField',key:"food"};
if(!(Number.isSafeInteger(f["food"])&&f["food"]>=0))return {why:'malformed',key:"food"};
if(!Object.hasOwn(f,"gold"))return {why:'missingField',key:"gold"};
if(!(Number.isSafeInteger(f["gold"])&&f["gold"]>=0))return {why:'malformed',key:"gold"};
if(!Object.hasOwn(f,"axe"))return {why:'missingField',key:"axe"};
if(!(typeof f["axe"]==='boolean'))return {why:'malformed',key:"axe"};
if(!Object.hasOwn(f,"boat"))return {why:'missingField',key:"boat"};
if(!(typeof f["boat"]==='boolean'))return {why:'malformed',key:"boat"};
if(!Object.hasOwn(f,"action"))return {why:'missingField',key:"action"};
if(!(Number.isSafeInteger(f["action"])&&f["action"]>=0))return {why:'malformed',key:"action"};
if(!Object.hasOwn(f,"reward"))return {why:'missingField',key:"reward"};
if(!(f["reward"]===null||(typeof f["reward"]==='number'&&Number.isFinite(f["reward"])&&Number.isFinite(Math.fround(f["reward"])))))return {why:'malformed',key:"reward"};
if(!Object.hasOwn(f,"done"))return {why:'missingField',key:"done"};
if(!(typeof f["done"]==='boolean'))return {why:'malformed',key:"done"};
if(!Object.hasOwn(f,"ev"))return {why:'missingField',key:"ev"};
if(!(Number.isSafeInteger(f["ev"])&&f["ev"]>=0))return {why:'malformed',key:"ev"};
if(!Object.hasOwn(f,"goal"))return {why:'missingField',key:"goal"};
if(!(Number.isSafeInteger(f["goal"])&&f["goal"]>=0))return {why:'malformed',key:"goal"};
if(!Object.hasOwn(f,"attempt"))return {why:'missingField',key:"attempt"};
if(!(Number.isSafeInteger(f["attempt"])&&f["attempt"]>=0))return {why:'malformed',key:"attempt"};
if(!Object.hasOwn(f,"tier"))return {why:'missingField',key:"tier"};
if(!(Number.isSafeInteger(f["tier"])&&f["tier"]>=0))return {why:'malformed',key:"tier"};
if(!Object.hasOwn(f,"cycle"))return {why:'missingField',key:"cycle"};
if(!(Number.isSafeInteger(f["cycle"])&&f["cycle"]>=0))return {why:'malformed',key:"cycle"};
if(!Object.hasOwn(f,"gkind"))return {why:'missingField',key:"gkind"};
if(![0,1,2,3,4].includes(f["gkind"]))return {why:'malformed',key:"gkind"};
if(!Object.hasOwn(f,"gitem"))return {why:'missingField',key:"gitem"};
if(![0,1,2,3,4,11,12].includes(f["gitem"]))return {why:'malformed',key:"gitem"};
if(!Object.hasOwn(f,"gx"))return {why:'missingField',key:"gx"};
if(!Number.isSafeInteger(f["gx"]))return {why:'malformed',key:"gx"};
if(!Object.hasOwn(f,"gy"))return {why:'missingField',key:"gy"};
if(!Number.isSafeInteger(f["gy"]))return {why:'malformed',key:"gy"};
if(!Object.hasOwn(f,"gn"))return {why:'missingField',key:"gn"};
if(!(Number.isSafeInteger(f["gn"])&&f["gn"]>=0))return {why:'malformed',key:"gn"};
if(!Object.hasOwn(f,"tiles"))return {why:'missingField',key:"tiles"};
if(Array.isArray(f["tiles"])&&f["tiles"].length!==121)return {why:'cardinality',key:"tiles"};
if(!(Array.isArray(f["tiles"])&&f["tiles"].length===121&&f["tiles"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"tiles"};
if(!Object.hasOwn(f,"tile_extra"))return {why:'missingField',key:"tile_extra"};
if(Array.isArray(f["tile_extra"])&&f["tile_extra"].length!==121)return {why:'cardinality',key:"tile_extra"};
if(!(Array.isArray(f["tile_extra"])&&f["tile_extra"].length===121&&f["tile_extra"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"tile_extra"};
if(!Object.hasOwn(f,"end"))return {why:'missingField',key:"end"};
if(!(typeof f["end"]==='boolean'))return {why:'malformed',key:"end"};
if(!Object.hasOwn(f,"lifetime_step"))return {why:'missingField',key:"lifetime_step"};
if(!(Number.isSafeInteger(f["lifetime_step"])&&f["lifetime_step"]>=0))return {why:'malformed',key:"lifetime_step"};
if(!Object.hasOwn(f,"reward_rate"))return {why:'missingField',key:"reward_rate"};
if(!(f["reward_rate"]===null||(typeof f["reward_rate"]==='number'&&Number.isFinite(f["reward_rate"])&&Number.isFinite(Math.fround(f["reward_rate"])))))return {why:'malformed',key:"reward_rate"};
if(!Object.hasOwn(f,"eps"))return {why:'missingField',key:"eps"};
if(!(f["eps"]===null||(typeof f["eps"]==='number'&&Number.isFinite(f["eps"])&&Number.isFinite(Math.fround(f["eps"])))))return {why:'malformed',key:"eps"};
if(!Object.hasOwn(f,"mean_alpha"))return {why:'missingField',key:"mean_alpha"};
if(!(f["mean_alpha"]===null||(typeof f["mean_alpha"]==='number'&&Number.isFinite(f["mean_alpha"])&&Number.isFinite(Math.fround(f["mean_alpha"])))))return {why:'malformed',key:"mean_alpha"};
if(!Object.hasOwn(f,"a_ctl"))return {why:'missingField',key:"a_ctl"};
if(!(f["a_ctl"]===null||(typeof f["a_ctl"]==='number'&&Number.isFinite(f["a_ctl"])&&Number.isFinite(Math.fround(f["a_ctl"])))))return {why:'malformed',key:"a_ctl"};
if(!Object.hasOwn(f,"a_dem"))return {why:'missingField',key:"a_dem"};
if(!(f["a_dem"]===null||(typeof f["a_dem"]==='number'&&Number.isFinite(f["a_dem"])&&Number.isFinite(Math.fround(f["a_dem"])))))return {why:'malformed',key:"a_dem"};
if(!Object.hasOwn(f,"alpha_control_all"))return {why:'missingField',key:"alpha_control_all"};
if(Array.isArray(f["alpha_control_all"])&&f["alpha_control_all"].length!==9)return {why:'cardinality',key:"alpha_control_all"};
if(!(Array.isArray(f["alpha_control_all"])&&f["alpha_control_all"].length===9&&f["alpha_control_all"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"alpha_control_all"};
if(!Object.hasOwn(f,"alpha_meta_all"))return {why:'missingField',key:"alpha_meta_all"};
if(Array.isArray(f["alpha_meta_all"])&&f["alpha_meta_all"].length!==4)return {why:'cardinality',key:"alpha_meta_all"};
if(!(Array.isArray(f["alpha_meta_all"])&&f["alpha_meta_all"].length===4&&f["alpha_meta_all"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"alpha_meta_all"};
if(!Object.hasOwn(f,"alpha_option_all"))return {why:'missingField',key:"alpha_option_all"};
if(Array.isArray(f["alpha_option_all"])&&f["alpha_option_all"].length!==27)return {why:'cardinality',key:"alpha_option_all"};
if(!(Array.isArray(f["alpha_option_all"])&&f["alpha_option_all"].length===27&&f["alpha_option_all"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"alpha_option_all"};
if(!Object.hasOwn(f,"alpha_demon_all"))return {why:'missingField',key:"alpha_demon_all"};
if(Array.isArray(f["alpha_demon_all"])&&f["alpha_demon_all"].length!==11)return {why:'cardinality',key:"alpha_demon_all"};
if(!(Array.isArray(f["alpha_demon_all"])&&f["alpha_demon_all"].length===11&&f["alpha_demon_all"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"alpha_demon_all"};
if(!Object.hasOwn(f,"alpha_models"))return {why:'missingField',key:"alpha_models"};
if(Array.isArray(f["alpha_models"])&&f["alpha_models"].length!==9)return {why:'cardinality',key:"alpha_models"};
if(!(Array.isArray(f["alpha_models"])&&f["alpha_models"].length===9&&f["alpha_models"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"alpha_models"};
if(!Object.hasOwn(f,"credit_control"))return {why:'missingField',key:"credit_control"};
if(Array.isArray(f["credit_control"])&&f["credit_control"].length!==9)return {why:'cardinality',key:"credit_control"};
if(!(Array.isArray(f["credit_control"])&&f["credit_control"].length===9&&f["credit_control"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"credit_control"};
if(!Object.hasOwn(f,"credit_meta"))return {why:'missingField',key:"credit_meta"};
if(Array.isArray(f["credit_meta"])&&f["credit_meta"].length!==4)return {why:'cardinality',key:"credit_meta"};
if(!(Array.isArray(f["credit_meta"])&&f["credit_meta"].length===4&&f["credit_meta"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"credit_meta"};
if(!Object.hasOwn(f,"credit_options"))return {why:'missingField',key:"credit_options"};
if(Array.isArray(f["credit_options"])&&f["credit_options"].length!==27)return {why:'cardinality',key:"credit_options"};
if(!(Array.isArray(f["credit_options"])&&f["credit_options"].length===27&&f["credit_options"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"credit_options"};
if(!Object.hasOwn(f,"credit_demons"))return {why:'missingField',key:"credit_demons"};
if(Array.isArray(f["credit_demons"])&&f["credit_demons"].length!==11)return {why:'cardinality',key:"credit_demons"};
if(!(Array.isArray(f["credit_demons"])&&f["credit_demons"].length===11&&f["credit_demons"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"credit_demons"};
if(!Object.hasOwn(f,"credit_models"))return {why:'missingField',key:"credit_models"};
if(Array.isArray(f["credit_models"])&&f["credit_models"].length!==9)return {why:'cardinality',key:"credit_models"};
if(!(Array.isArray(f["credit_models"])&&f["credit_models"].length===9&&f["credit_models"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"credit_models"};
if(!Object.hasOwn(f,"option_model_rewards"))return {why:'missingField',key:"option_model_rewards"};
if(Array.isArray(f["option_model_rewards"])&&f["option_model_rewards"].length!==3)return {why:'cardinality',key:"option_model_rewards"};
if(!(Array.isArray(f["option_model_rewards"])&&f["option_model_rewards"].length===3&&f["option_model_rewards"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"option_model_rewards"};
if(!Object.hasOwn(f,"option_model_continuations"))return {why:'missingField',key:"option_model_continuations"};
if(Array.isArray(f["option_model_continuations"])&&f["option_model_continuations"].length!==3)return {why:'cardinality',key:"option_model_continuations"};
if(!(Array.isArray(f["option_model_continuations"])&&f["option_model_continuations"].length===3&&f["option_model_continuations"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"option_model_continuations"};
if(!Object.hasOwn(f,"option_model_durations"))return {why:'missingField',key:"option_model_durations"};
if(Array.isArray(f["option_model_durations"])&&f["option_model_durations"].length!==3)return {why:'cardinality',key:"option_model_durations"};
if(!(Array.isArray(f["option_model_durations"])&&f["option_model_durations"].length===3&&f["option_model_durations"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"option_model_durations"};
if(!Object.hasOwn(f,"planning_errors"))return {why:'missingField',key:"planning_errors"};
if(Array.isArray(f["planning_errors"])&&f["planning_errors"].length!==3)return {why:'cardinality',key:"planning_errors"};
if(!(Array.isArray(f["planning_errors"])&&f["planning_errors"].length===3&&f["planning_errors"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"planning_errors"};
if(!Object.hasOwn(f,"planning_steps"))return {why:'missingField',key:"planning_steps"};
if(!(Number.isSafeInteger(f["planning_steps"])&&f["planning_steps"]>=0))return {why:'malformed',key:"planning_steps"};
if(!Object.hasOwn(f,"decision_source"))return {why:'missingField',key:"decision_source"};
if(!(typeof f["decision_source"]==='string'))return {why:'malformed',key:"decision_source"};
if(!Object.hasOwn(f,"skill"))return {why:'missingField',key:"skill"};
if(!(Number.isSafeInteger(f["skill"])&&f["skill"]>=0))return {why:'malformed',key:"skill"};
if(!Object.hasOwn(f,"explored"))return {why:'missingField',key:"explored"};
if(!(typeof f["explored"]==='boolean'))return {why:'malformed',key:"explored"};
if(!Object.hasOwn(f,"control"))return {why:'missingField',key:"control"};
if(Array.isArray(f["control"])&&f["control"].length!==9)return {why:'cardinality',key:"control"};
if(!(Array.isArray(f["control"])&&f["control"].length===9&&f["control"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"control"};
if(!Object.hasOwn(f,"meta"))return {why:'missingField',key:"meta"};
if(Array.isArray(f["meta"])&&f["meta"].length!==4)return {why:'cardinality',key:"meta"};
if(!(Array.isArray(f["meta"])&&f["meta"].length===4&&f["meta"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"meta"};
if(!Object.hasOwn(f,"action_probabilities"))return {why:'missingField',key:"action_probabilities"};
if(Array.isArray(f["action_probabilities"])&&f["action_probabilities"].length!==9)return {why:'cardinality',key:"action_probabilities"};
if(!(Array.isArray(f["action_probabilities"])&&f["action_probabilities"].length===9&&f["action_probabilities"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"action_probabilities"};
if(!Object.hasOwn(f,"meta_probabilities"))return {why:'missingField',key:"meta_probabilities"};
if(Array.isArray(f["meta_probabilities"])&&f["meta_probabilities"].length!==4)return {why:'cardinality',key:"meta_probabilities"};
if(!(Array.isArray(f["meta_probabilities"])&&f["meta_probabilities"].length===4&&f["meta_probabilities"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"meta_probabilities"};
if(!Object.hasOwn(f,"meta_action"))return {why:'missingField',key:"meta_action"};
if(!(Number.isSafeInteger(f["meta_action"])&&f["meta_action"]>=0))return {why:'malformed',key:"meta_action"};
if(!Object.hasOwn(f,"option_start"))return {why:'missingField',key:"option_start"};
if(!(Number.isSafeInteger(f["option_start"])&&f["option_start"]>=0))return {why:'malformed',key:"option_start"};
if(!Object.hasOwn(f,"option_end_skill"))return {why:'missingField',key:"option_end_skill"};
if(!(Number.isSafeInteger(f["option_end_skill"])&&f["option_end_skill"]>=0))return {why:'malformed',key:"option_end_skill"};
if(!Object.hasOwn(f,"option_end_duration"))return {why:'missingField',key:"option_end_duration"};
if(!(Number.isSafeInteger(f["option_end_duration"])&&f["option_end_duration"]>=0))return {why:'malformed',key:"option_end_duration"};
if(!Object.hasOwn(f,"option_end_reason"))return {why:'missingField',key:"option_end_reason"};
if(!(Number.isSafeInteger(f["option_end_reason"])&&f["option_end_reason"]>=0))return {why:'malformed',key:"option_end_reason"};
if(!Object.hasOwn(f,"option_elapsed"))return {why:'missingField',key:"option_elapsed"};
if(!(Number.isSafeInteger(f["option_elapsed"])&&f["option_elapsed"]>=0))return {why:'malformed',key:"option_elapsed"};
if(!Object.hasOwn(f,"lifetime_reward_sum"))return {why:'missingField',key:"lifetime_reward_sum"};
if(!(f["lifetime_reward_sum"]===null||(typeof f["lifetime_reward_sum"]==='number'&&Number.isFinite(f["lifetime_reward_sum"]))))return {why:'malformed',key:"lifetime_reward_sum"};
if(!Object.hasOwn(f,"lifetime_reward_count"))return {why:'missingField',key:"lifetime_reward_count"};
if(!(Number.isSafeInteger(f["lifetime_reward_count"])&&f["lifetime_reward_count"]>=0))return {why:'malformed',key:"lifetime_reward_count"};
if(!Object.hasOwn(f,"lifetime_reward_family_sum"))return {why:'missingField',key:"lifetime_reward_family_sum"};
if(Array.isArray(f["lifetime_reward_family_sum"])&&f["lifetime_reward_family_sum"].length!==4)return {why:'cardinality',key:"lifetime_reward_family_sum"};
if(!(Array.isArray(f["lifetime_reward_family_sum"])&&f["lifetime_reward_family_sum"].length===4&&f["lifetime_reward_family_sum"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v))))))return {why:'malformed',key:"lifetime_reward_family_sum"};
if(!Object.hasOwn(f,"lifetime_reward_family_count"))return {why:'missingField',key:"lifetime_reward_family_count"};
if(Array.isArray(f["lifetime_reward_family_count"])&&f["lifetime_reward_family_count"].length!==4)return {why:'cardinality',key:"lifetime_reward_family_count"};
if(!(Array.isArray(f["lifetime_reward_family_count"])&&f["lifetime_reward_family_count"].length===4&&f["lifetime_reward_family_count"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_reward_family_count"};
if(!Object.hasOwn(f,"lifetime_reward_history_sum"))return {why:'missingField',key:"lifetime_reward_history_sum"};
if(Array.isArray(f["lifetime_reward_history_sum"])&&f["lifetime_reward_history_sum"].length!==64)return {why:'cardinality',key:"lifetime_reward_history_sum"};
if(!(Array.isArray(f["lifetime_reward_history_sum"])&&f["lifetime_reward_history_sum"].length===64&&f["lifetime_reward_history_sum"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v))))))return {why:'malformed',key:"lifetime_reward_history_sum"};
if(!Object.hasOwn(f,"lifetime_reward_history_count"))return {why:'missingField',key:"lifetime_reward_history_count"};
if(Array.isArray(f["lifetime_reward_history_count"])&&f["lifetime_reward_history_count"].length!==64)return {why:'cardinality',key:"lifetime_reward_history_count"};
if(!(Array.isArray(f["lifetime_reward_history_count"])&&f["lifetime_reward_history_count"].length===64&&f["lifetime_reward_history_count"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_reward_history_count"};
if(!Object.hasOwn(f,"lifetime_error_history_sum"))return {why:'missingField',key:"lifetime_error_history_sum"};
if(Array.isArray(f["lifetime_error_history_sum"])&&f["lifetime_error_history_sum"].length!==64)return {why:'cardinality',key:"lifetime_error_history_sum"};
if(!(Array.isArray(f["lifetime_error_history_sum"])&&f["lifetime_error_history_sum"].length===64&&f["lifetime_error_history_sum"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v))))))return {why:'malformed',key:"lifetime_error_history_sum"};
if(!Object.hasOwn(f,"lifetime_error_history_count"))return {why:'missingField',key:"lifetime_error_history_count"};
if(Array.isArray(f["lifetime_error_history_count"])&&f["lifetime_error_history_count"].length!==64)return {why:'cardinality',key:"lifetime_error_history_count"};
if(!(Array.isArray(f["lifetime_error_history_count"])&&f["lifetime_error_history_count"].length===64&&f["lifetime_error_history_count"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_error_history_count"};
if(!Object.hasOwn(f,"lifetime_error_sum"))return {why:'missingField',key:"lifetime_error_sum"};
if(Array.isArray(f["lifetime_error_sum"])&&f["lifetime_error_sum"].length!==11)return {why:'cardinality',key:"lifetime_error_sum"};
if(!(Array.isArray(f["lifetime_error_sum"])&&f["lifetime_error_sum"].length===11&&f["lifetime_error_sum"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v))))))return {why:'malformed',key:"lifetime_error_sum"};
if(!Object.hasOwn(f,"lifetime_error_count"))return {why:'missingField',key:"lifetime_error_count"};
if(Array.isArray(f["lifetime_error_count"])&&f["lifetime_error_count"].length!==11)return {why:'cardinality',key:"lifetime_error_count"};
if(!(Array.isArray(f["lifetime_error_count"])&&f["lifetime_error_count"].length===11&&f["lifetime_error_count"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_error_count"};
if(!Object.hasOwn(f,"settled_return"))return {why:'missingField',key:"settled_return"};
if(Array.isArray(f["settled_return"])&&f["settled_return"].length!==11)return {why:'cardinality',key:"settled_return"};
if(!(Array.isArray(f["settled_return"])&&f["settled_return"].length===11&&f["settled_return"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"settled_return"};
if(!Object.hasOwn(f,"settled_error"))return {why:'missingField',key:"settled_error"};
if(Array.isArray(f["settled_error"])&&f["settled_error"].length!==11)return {why:'cardinality',key:"settled_error"};
if(!(Array.isArray(f["settled_error"])&&f["settled_error"].length===11&&f["settled_error"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"settled_error"};
if(!Object.hasOwn(f,"lifetime_option_started"))return {why:'missingField',key:"lifetime_option_started"};
if(Array.isArray(f["lifetime_option_started"])&&f["lifetime_option_started"].length!==3)return {why:'cardinality',key:"lifetime_option_started"};
if(!(Array.isArray(f["lifetime_option_started"])&&f["lifetime_option_started"].length===3&&f["lifetime_option_started"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_option_started"};
if(!Object.hasOwn(f,"lifetime_option_completed"))return {why:'missingField',key:"lifetime_option_completed"};
if(Array.isArray(f["lifetime_option_completed"])&&f["lifetime_option_completed"].length!==3)return {why:'cardinality',key:"lifetime_option_completed"};
if(!(Array.isArray(f["lifetime_option_completed"])&&f["lifetime_option_completed"].length===3&&f["lifetime_option_completed"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_option_completed"};
if(!Object.hasOwn(f,"lifetime_option_duration"))return {why:'missingField',key:"lifetime_option_duration"};
if(Array.isArray(f["lifetime_option_duration"])&&f["lifetime_option_duration"].length!==3)return {why:'cardinality',key:"lifetime_option_duration"};
if(!(Array.isArray(f["lifetime_option_duration"])&&f["lifetime_option_duration"].length===3&&f["lifetime_option_duration"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_option_duration"};
if(!Object.hasOwn(f,"lifetime_option_end_reasons"))return {why:'missingField',key:"lifetime_option_end_reasons"};
if(Array.isArray(f["lifetime_option_end_reasons"])&&f["lifetime_option_end_reasons"].length!==9)return {why:'cardinality',key:"lifetime_option_end_reasons"};
if(!(Array.isArray(f["lifetime_option_end_reasons"])&&f["lifetime_option_end_reasons"].length===9&&f["lifetime_option_end_reasons"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_option_end_reasons"};
if(!Object.hasOwn(f,"lifetime_goal_attempts"))return {why:'missingField',key:"lifetime_goal_attempts"};
if(Array.isArray(f["lifetime_goal_attempts"])&&f["lifetime_goal_attempts"].length!==4)return {why:'cardinality',key:"lifetime_goal_attempts"};
if(!(Array.isArray(f["lifetime_goal_attempts"])&&f["lifetime_goal_attempts"].length===4&&f["lifetime_goal_attempts"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_goal_attempts"};
if(!Object.hasOwn(f,"lifetime_goal_successes"))return {why:'missingField',key:"lifetime_goal_successes"};
if(Array.isArray(f["lifetime_goal_successes"])&&f["lifetime_goal_successes"].length!==4)return {why:'cardinality',key:"lifetime_goal_successes"};
if(!(Array.isArray(f["lifetime_goal_successes"])&&f["lifetime_goal_successes"].length===4&&f["lifetime_goal_successes"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_goal_successes"};
if(!Object.hasOwn(f,"lifetime_goal_steps"))return {why:'missingField',key:"lifetime_goal_steps"};
if(Array.isArray(f["lifetime_goal_steps"])&&f["lifetime_goal_steps"].length!==4)return {why:'cardinality',key:"lifetime_goal_steps"};
if(!(Array.isArray(f["lifetime_goal_steps"])&&f["lifetime_goal_steps"].length===4&&f["lifetime_goal_steps"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_goal_steps"};
if(!Object.hasOwn(f,"lifetime_cycle_attempts"))return {why:'missingField',key:"lifetime_cycle_attempts"};
if(Array.isArray(f["lifetime_cycle_attempts"])&&f["lifetime_cycle_attempts"].length!==64)return {why:'cardinality',key:"lifetime_cycle_attempts"};
if(!(Array.isArray(f["lifetime_cycle_attempts"])&&f["lifetime_cycle_attempts"].length===64&&f["lifetime_cycle_attempts"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_cycle_attempts"};
if(!Object.hasOwn(f,"lifetime_cycle_successes"))return {why:'missingField',key:"lifetime_cycle_successes"};
if(Array.isArray(f["lifetime_cycle_successes"])&&f["lifetime_cycle_successes"].length!==64)return {why:'cardinality',key:"lifetime_cycle_successes"};
if(!(Array.isArray(f["lifetime_cycle_successes"])&&f["lifetime_cycle_successes"].length===64&&f["lifetime_cycle_successes"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_cycle_successes"};
if(!Object.hasOwn(f,"lifetime_cycle_steps"))return {why:'missingField',key:"lifetime_cycle_steps"};
if(Array.isArray(f["lifetime_cycle_steps"])&&f["lifetime_cycle_steps"].length!==64)return {why:'cardinality',key:"lifetime_cycle_steps"};
if(!(Array.isArray(f["lifetime_cycle_steps"])&&f["lifetime_cycle_steps"].length===64&&f["lifetime_cycle_steps"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"lifetime_cycle_steps"};
if(!Object.hasOwn(f,"agreement_version"))return {why:'missingField',key:"agreement_version"};
if(!(Number.isSafeInteger(f["agreement_version"])&&f["agreement_version"]>=0))return {why:'malformed',key:"agreement_version"};
if(!Object.hasOwn(f,"agreement_scale"))return {why:'missingField',key:"agreement_scale"};
if(!(Number.isSafeInteger(f["agreement_scale"])&&f["agreement_scale"]>=0))return {why:'malformed',key:"agreement_scale"};
if(!Object.hasOwn(f,"agreement_started"))return {why:'missingField',key:"agreement_started"};
if(!(f["agreement_started"]===null||(Number.isSafeInteger(f["agreement_started"])&&f["agreement_started"]>=0)))return {why:'malformed',key:"agreement_started"};
if(!Object.hasOwn(f,"agreement_stopped"))return {why:'missingField',key:"agreement_stopped"};
if(!(typeof f["agreement_stopped"]==='boolean'))return {why:'malformed',key:"agreement_stopped"};
if(!Object.hasOwn(f,"agreement_score"))return {why:'missingField',key:"agreement_score"};
if(!(f["agreement_score"]===null||(Number.isSafeInteger(f["agreement_score"])&&f["agreement_score"]>=0)))return {why:'malformed',key:"agreement_score"};
if(!Object.hasOwn(f,"agreement_text"))return {why:'missingField',key:"agreement_text"};
if(!(f["agreement_text"]===null||(typeof f["agreement_text"]==='string')))return {why:'malformed',key:"agreement_text"};
if(!Object.hasOwn(f,"agreement_error"))return {why:'missingField',key:"agreement_error"};
if(!(f["agreement_error"]===null||(Number.isSafeInteger(f["agreement_error"])&&f["agreement_error"]>=0)))return {why:'malformed',key:"agreement_error"};
if(!Object.hasOwn(f,"agreement_channel_score"))return {why:'missingField',key:"agreement_channel_score"};
if(Array.isArray(f["agreement_channel_score"])&&f["agreement_channel_score"].length!==11)return {why:'cardinality',key:"agreement_channel_score"};
if(!(Array.isArray(f["agreement_channel_score"])&&f["agreement_channel_score"].length===11&&f["agreement_channel_score"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_channel_score"};
if(!Object.hasOwn(f,"agreement_channel_text"))return {why:'missingField',key:"agreement_channel_text"};
if(Array.isArray(f["agreement_channel_text"])&&f["agreement_channel_text"].length!==11)return {why:'cardinality',key:"agreement_channel_text"};
if(!(Array.isArray(f["agreement_channel_text"])&&f["agreement_channel_text"].length===11&&f["agreement_channel_text"].every(v=>(v===null||(typeof v==='string')))))return {why:'malformed',key:"agreement_channel_text"};
if(!Object.hasOwn(f,"agreement_channel_error"))return {why:'missingField',key:"agreement_channel_error"};
if(Array.isArray(f["agreement_channel_error"])&&f["agreement_channel_error"].length!==11)return {why:'cardinality',key:"agreement_channel_error"};
if(!(Array.isArray(f["agreement_channel_error"])&&f["agreement_channel_error"].length===11&&f["agreement_channel_error"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_channel_error"};
if(!Object.hasOwn(f,"agreement_count"))return {why:'missingField',key:"agreement_count"};
if(Array.isArray(f["agreement_count"])&&f["agreement_count"].length!==11)return {why:'cardinality',key:"agreement_count"};
if(!(Array.isArray(f["agreement_count"])&&f["agreement_count"].length===11&&f["agreement_count"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"agreement_count"};
if(!Object.hasOwn(f,"agreement_pending"))return {why:'missingField',key:"agreement_pending"};
if(Array.isArray(f["agreement_pending"])&&f["agreement_pending"].length!==11)return {why:'cardinality',key:"agreement_pending"};
if(!(Array.isArray(f["agreement_pending"])&&f["agreement_pending"].length===11&&f["agreement_pending"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"agreement_pending"};
if(!Object.hasOwn(f,"agreement_censored"))return {why:'missingField',key:"agreement_censored"};
if(Array.isArray(f["agreement_censored"])&&f["agreement_censored"].length!==11)return {why:'cardinality',key:"agreement_censored"};
if(!(Array.isArray(f["agreement_censored"])&&f["agreement_censored"].length===11&&f["agreement_censored"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"agreement_censored"};
if(!Object.hasOwn(f,"agreement_status"))return {why:'missingField',key:"agreement_status"};
if(Array.isArray(f["agreement_status"])&&f["agreement_status"].length!==11)return {why:'cardinality',key:"agreement_status"};
if(!(Array.isArray(f["agreement_status"])&&f["agreement_status"].length===11&&f["agreement_status"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"agreement_status"};
if(!Object.hasOwn(f,"agreement_horizon"))return {why:'missingField',key:"agreement_horizon"};
if(Array.isArray(f["agreement_horizon"])&&f["agreement_horizon"].length!==11)return {why:'cardinality',key:"agreement_horizon"};
if(!(Array.isArray(f["agreement_horizon"])&&f["agreement_horizon"].length===11&&f["agreement_horizon"].every(v=>(Number.isSafeInteger(v)&&v>=0))))return {why:'malformed',key:"agreement_horizon"};
if(!Object.hasOwn(f,"agreement_start_first"))return {why:'missingField',key:"agreement_start_first"};
if(Array.isArray(f["agreement_start_first"])&&f["agreement_start_first"].length!==11)return {why:'cardinality',key:"agreement_start_first"};
if(!(Array.isArray(f["agreement_start_first"])&&f["agreement_start_first"].length===11&&f["agreement_start_first"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_start_first"};
if(!Object.hasOwn(f,"agreement_start_last"))return {why:'missingField',key:"agreement_start_last"};
if(Array.isArray(f["agreement_start_last"])&&f["agreement_start_last"].length!==11)return {why:'cardinality',key:"agreement_start_last"};
if(!(Array.isArray(f["agreement_start_last"])&&f["agreement_start_last"].length===11&&f["agreement_start_last"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_start_last"};
if(!Object.hasOwn(f,"agreement_settlement_first"))return {why:'missingField',key:"agreement_settlement_first"};
if(Array.isArray(f["agreement_settlement_first"])&&f["agreement_settlement_first"].length!==11)return {why:'cardinality',key:"agreement_settlement_first"};
if(!(Array.isArray(f["agreement_settlement_first"])&&f["agreement_settlement_first"].length===11&&f["agreement_settlement_first"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_settlement_first"};
if(!Object.hasOwn(f,"agreement_settlement_last"))return {why:'missingField',key:"agreement_settlement_last"};
if(Array.isArray(f["agreement_settlement_last"])&&f["agreement_settlement_last"].length!==11)return {why:'cardinality',key:"agreement_settlement_last"};
if(!(Array.isArray(f["agreement_settlement_last"])&&f["agreement_settlement_last"].length===11&&f["agreement_settlement_last"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_settlement_last"};
if(!Object.hasOwn(f,"agreement_tail"))return {why:'missingField',key:"agreement_tail"};
if(Array.isArray(f["agreement_tail"])&&f["agreement_tail"].length!==11)return {why:'cardinality',key:"agreement_tail"};
if(!(Array.isArray(f["agreement_tail"])&&f["agreement_tail"].length===11&&f["agreement_tail"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_tail"};
if(!Object.hasOwn(f,"agreement_rounding"))return {why:'missingField',key:"agreement_rounding"};
if(Array.isArray(f["agreement_rounding"])&&f["agreement_rounding"].length!==11)return {why:'cardinality',key:"agreement_rounding"};
if(!(Array.isArray(f["agreement_rounding"])&&f["agreement_rounding"].length===11&&f["agreement_rounding"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_rounding"};
if(!Object.hasOwn(f,"agreement_history_clock"))return {why:'missingField',key:"agreement_history_clock"};
if(Array.isArray(f["agreement_history_clock"])&&f["agreement_history_clock"].length!==64)return {why:'cardinality',key:"agreement_history_clock"};
if(!(Array.isArray(f["agreement_history_clock"])&&f["agreement_history_clock"].length===64&&f["agreement_history_clock"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_history_clock"};
if(!Object.hasOwn(f,"agreement_history_score"))return {why:'missingField',key:"agreement_history_score"};
if(Array.isArray(f["agreement_history_score"])&&f["agreement_history_score"].length!==64)return {why:'cardinality',key:"agreement_history_score"};
if(!(Array.isArray(f["agreement_history_score"])&&f["agreement_history_score"].length===64&&f["agreement_history_score"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"agreement_history_score"};
if(!Object.hasOwn(f,"checkpoint_format"))return {why:'missingField',key:"checkpoint_format"};
if(!(Number.isSafeInteger(f["checkpoint_format"])&&f["checkpoint_format"]>=0))return {why:'malformed',key:"checkpoint_format"};
if(!Object.hasOwn(f,"control_criterion"))return {why:'missingField',key:"control_criterion"};
if(!(Number.isSafeInteger(f["control_criterion"])&&f["control_criterion"]>=0))return {why:'malformed',key:"control_criterion"};
if(!Object.hasOwn(f,"weight_space"))return {why:'missingField',key:"weight_space"};
if(!(Number.isSafeInteger(f["weight_space"])&&f["weight_space"]>=0))return {why:'malformed',key:"weight_space"};
if(!Object.hasOwn(f,"primitive_count"))return {why:'missingField',key:"primitive_count"};
if(!(Number.isSafeInteger(f["primitive_count"])&&f["primitive_count"]>=0))return {why:'malformed',key:"primitive_count"};
if(!Object.hasOwn(f,"meta_count"))return {why:'missingField',key:"meta_count"};
if(!(Number.isSafeInteger(f["meta_count"])&&f["meta_count"]>=0))return {why:'malformed',key:"meta_count"};
if(!Object.hasOwn(f,"skill_count"))return {why:'missingField',key:"skill_count"};
if(!(Number.isSafeInteger(f["skill_count"])&&f["skill_count"]>=0))return {why:'malformed',key:"skill_count"};
if(!Object.hasOwn(f,"option_end_count"))return {why:'missingField',key:"option_end_count"};
if(!(Number.isSafeInteger(f["option_end_count"])&&f["option_end_count"]>=0))return {why:'malformed',key:"option_end_count"};
if(!Object.hasOwn(f,"demon_count"))return {why:'missingField',key:"demon_count"};
if(!(Number.isSafeInteger(f["demon_count"])&&f["demon_count"]>=0))return {why:'malformed',key:"demon_count"};
if(!Object.hasOwn(f,"learner_count"))return {why:'missingField',key:"learner_count"};
if(!(Number.isSafeInteger(f["learner_count"])&&f["learner_count"]>=0))return {why:'malformed',key:"learner_count"};
if(!Object.hasOwn(f,"history_bins"))return {why:'missingField',key:"history_bins"};
if(!(Number.isSafeInteger(f["history_bins"])&&f["history_bins"]>=0))return {why:'malformed',key:"history_bins"};
if(!Object.hasOwn(f,"cycle_bins"))return {why:'missingField',key:"cycle_bins"};
if(!(Number.isSafeInteger(f["cycle_bins"])&&f["cycle_bins"]>=0))return {why:'malformed',key:"cycle_bins"};
if(!Object.hasOwn(f,"exact_cycles"))return {why:'missingField',key:"exact_cycles"};
if(!(Number.isSafeInteger(f["exact_cycles"])&&f["exact_cycles"]>=0))return {why:'malformed',key:"exact_cycles"};
if(!Object.hasOwn(f,"settle_stride"))return {why:'missingField',key:"settle_stride"};
if(!(Number.isSafeInteger(f["settle_stride"])&&f["settle_stride"]>=0))return {why:'malformed',key:"settle_stride"};
if(!Object.hasOwn(f,"settle_remaining"))return {why:'missingField',key:"settle_remaining"};
if(!(f["settle_remaining"]===null||(typeof f["settle_remaining"]==='number'&&Number.isFinite(f["settle_remaining"])&&Number.isFinite(Math.fround(f["settle_remaining"])))))return {why:'malformed',key:"settle_remaining"};
if(!Object.hasOwn(f,"n_tilings"))return {why:'missingField',key:"n_tilings"};
if(!(Number.isSafeInteger(f["n_tilings"])&&f["n_tilings"]>=0))return {why:'malformed',key:"n_tilings"};
if(!Object.hasOwn(f,"imprint_units"))return {why:'missingField',key:"imprint_units"};
if(!(Number.isSafeInteger(f["imprint_units"])&&f["imprint_units"]>=0))return {why:'malformed',key:"imprint_units"};
if(!Object.hasOwn(f,"retire_step"))return {why:'missingField',key:"retire_step"};
if(!(f["retire_step"]===null||(Number.isSafeInteger(f["retire_step"])&&f["retire_step"]>=0)))return {why:'malformed',key:"retire_step"};
if(!Object.hasOwn(f,"retire_unit"))return {why:'missingField',key:"retire_unit"};
if(!(f["retire_unit"]===null||(Number.isSafeInteger(f["retire_unit"])&&f["retire_unit"]>=0)))return {why:'malformed',key:"retire_unit"};
if(!Object.hasOwn(f,"retire_count"))return {why:'missingField',key:"retire_count"};
if(!(Number.isSafeInteger(f["retire_count"])&&f["retire_count"]>=0))return {why:'malformed',key:"retire_count"};
if(!Object.hasOwn(f,"subtask_policy"))return {why:'missingField',key:"subtask_policy"};
if(!(typeof f["subtask_policy"]==='string'))return {why:'malformed',key:"subtask_policy"};
if(!Object.hasOwn(f,"subtask_unit"))return {why:'missingField',key:"subtask_unit"};
if(Array.isArray(f["subtask_unit"])&&f["subtask_unit"].length!==3)return {why:'cardinality',key:"subtask_unit"};
if(!(Array.isArray(f["subtask_unit"])&&f["subtask_unit"].length===3&&f["subtask_unit"].every(v=>(v===null||(Number.isSafeInteger(v)&&v>=0)))))return {why:'malformed',key:"subtask_unit"};
if(!Object.hasOwn(f,"subtask_bonus"))return {why:'missingField',key:"subtask_bonus"};
if(Array.isArray(f["subtask_bonus"])&&f["subtask_bonus"].length!==3)return {why:'cardinality',key:"subtask_bonus"};
if(!(Array.isArray(f["subtask_bonus"])&&f["subtask_bonus"].length===3&&f["subtask_bonus"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"subtask_bonus"};
if(!Object.hasOwn(f,"action_names"))return {why:'missingField',key:"action_names"};
if(Array.isArray(f["action_names"])&&f["action_names"].length!==9)return {why:'cardinality',key:"action_names"};
if(!(Array.isArray(f["action_names"])&&f["action_names"].length===9&&f["action_names"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"action_names"};
if(!Object.hasOwn(f,"meta_names"))return {why:'missingField',key:"meta_names"};
if(Array.isArray(f["meta_names"])&&f["meta_names"].length!==4)return {why:'cardinality',key:"meta_names"};
if(!(Array.isArray(f["meta_names"])&&f["meta_names"].length===4&&f["meta_names"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"meta_names"};
if(!Object.hasOwn(f,"skill_names"))return {why:'missingField',key:"skill_names"};
if(Array.isArray(f["skill_names"])&&f["skill_names"].length!==3)return {why:'cardinality',key:"skill_names"};
if(!(Array.isArray(f["skill_names"])&&f["skill_names"].length===3&&f["skill_names"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"skill_names"};
if(!Object.hasOwn(f,"goal_family_names"))return {why:'missingField',key:"goal_family_names"};
if(Array.isArray(f["goal_family_names"])&&f["goal_family_names"].length!==4)return {why:'cardinality',key:"goal_family_names"};
if(!(Array.isArray(f["goal_family_names"])&&f["goal_family_names"].length===4&&f["goal_family_names"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"goal_family_names"};
if(!Object.hasOwn(f,"demons"))return {why:'missingField',key:"demons"};
if(Array.isArray(f["demons"])&&f["demons"].length!==11)return {why:'cardinality',key:"demons"};
if(!(Array.isArray(f["demons"])&&f["demons"].length===11&&f["demons"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"demons"};
if(!Object.hasOwn(f,"cums"))return {why:'missingField',key:"cums"};
if(Array.isArray(f["cums"])&&f["cums"].length!==11)return {why:'cardinality',key:"cums"};
if(!(Array.isArray(f["cums"])&&f["cums"].length===11&&f["cums"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"cums"};
if(!Object.hasOwn(f,"demon_names"))return {why:'missingField',key:"demon_names"};
if(Array.isArray(f["demon_names"])&&f["demon_names"].length!==11)return {why:'cardinality',key:"demon_names"};
if(!(Array.isArray(f["demon_names"])&&f["demon_names"].length===11&&f["demon_names"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"demon_names"};
if(!Object.hasOwn(f,"demon_target_policy"))return {why:'missingField',key:"demon_target_policy"};
if(Array.isArray(f["demon_target_policy"])&&f["demon_target_policy"].length!==11)return {why:'cardinality',key:"demon_target_policy"};
if(!(Array.isArray(f["demon_target_policy"])&&f["demon_target_policy"].length===11&&f["demon_target_policy"].every(v=>(typeof v==='string'))))return {why:'malformed',key:"demon_target_policy"};
if(!Object.hasOwn(f,"demon_gamma"))return {why:'missingField',key:"demon_gamma"};
if(Array.isArray(f["demon_gamma"])&&f["demon_gamma"].length!==11)return {why:'cardinality',key:"demon_gamma"};
if(!(Array.isArray(f["demon_gamma"])&&f["demon_gamma"].length===11&&f["demon_gamma"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"demon_gamma"};
if(!Object.hasOwn(f,"demon_horizon"))return {why:'missingField',key:"demon_horizon"};
if(Array.isArray(f["demon_horizon"])&&f["demon_horizon"].length!==11)return {why:'cardinality',key:"demon_horizon"};
if(!(Array.isArray(f["demon_horizon"])&&f["demon_horizon"].length===11&&f["demon_horizon"].every(v=>(v===null||(typeof v==='number'&&Number.isFinite(v)&&Number.isFinite(Math.fround(v)))))))return {why:'malformed',key:"demon_horizon"};
if(!(f["curriculum_names"].length===f["goal_count"]))return {why:"malformed",key:"curriculum_names"};
if(!(f["curriculum_failed_attempts"].length===f["goal_count"]))return {why:"malformed",key:"curriculum_failed_attempts"};
if(!(f["curriculum_success_steps"].length===f["goal_count"]))return {why:"malformed",key:"curriculum_success_steps"};
if(!f["curriculum_failed_attempts"].every(v=>(v===null||v<=f["attempt_cap"])))return {why:"malformed",key:"curriculum_failed_attempts"};
if(!f["curriculum_success_steps"].every(v=>(v===null||v<=f["step_cap"])))return {why:"malformed",key:"curriculum_success_steps"};
if(!(f["schema_version"]===10))return {why:"schema",key:"schema_version"};
if(!(f["goal_progress_score"]===null||(f["goal_progress_score"]>=0&&f["goal_progress_score"]<1001)))return {why:"malformed",key:"goal_progress_score"};
if(!(f["goal_progress_resolved"]===null||f["goal_progress_resolved"]<=f["goal_count"]))return {why:"malformed",key:"goal_progress_resolved"};
if(!(f["goal_progress_attempt"]===null||f["goal_progress_attempt"]<=f["attempt_cap"]))return {why:"malformed",key:"goal_progress_attempt"};
if(!(f["goal_progress_achieved"]===null||f["goal_progress_achieved"]<=f["goal_progress_resolved"]))return {why:"malformed",key:"goal_progress_achieved"};
if(!(f["goal_progress_completed_achieved"]===null||f["goal_progress_completed_achieved"]<=f["goal_count"]))return {why:"malformed",key:"goal_progress_completed_achieved"};
if(!(f["goal_progress_completed_cycle"]===null||f["goal_progress_completed_cycle"]<=f["goal_progress_cycle"]))return {why:"malformed",key:"goal_progress_completed_cycle"};
if(!(f["agreement_version"]===1))return {why:"cardinality",key:"agreement_version"};
if(!(f["agreement_scale"]===1000000))return {why:"cardinality",key:"agreement_scale"};
if(!(f["agreement_score"]===null||(f["agreement_score"]>=0&&f["agreement_score"]<1000001)))return {why:"malformed",key:"agreement_score"};
if(!(f["agreement_error"]===null||(f["agreement_error"]>=0&&f["agreement_error"]<1000001)))return {why:"malformed",key:"agreement_error"};
if(!f["agreement_channel_score"].every(v=>(v===null||(v>=0&&v<1000001))))return {why:"malformed",key:"agreement_channel_score"};
if(!f["agreement_channel_error"].every(v=>(v===null||(v>=0&&v<1000001))))return {why:"malformed",key:"agreement_channel_error"};
if(!f["agreement_pending"].every(v=>(v>=0&&v<27)))return {why:"malformed",key:"agreement_pending"};
if(!f["agreement_count"].every(v=>(typeof v==='string'&&v.length<=20&&/^(0|[1-9][0-9]*)$/.test(v)&&BigInt(v)<=BigInt('18446744073709551615'))))return {why:"malformed",key:"agreement_count"};
if(!f["agreement_censored"].every(v=>(typeof v==='string'&&v.length<=20&&/^(0|[1-9][0-9]*)$/.test(v)&&BigInt(v)<=BigInt('18446744073709551615'))))return {why:"malformed",key:"agreement_censored"};
if(!f["agreement_horizon"].every(v=>(v>=0&&v<601)))return {why:"malformed",key:"agreement_horizon"};
if(!f["agreement_tail"].every(v=>(v===null||(v>=0&&v<1000001))))return {why:"malformed",key:"agreement_tail"};
if(!f["agreement_rounding"].every(v=>(v===null||(v>=0&&v<1000001))))return {why:"malformed",key:"agreement_rounding"};
if(!f["agreement_history_score"].every(v=>(v===null||(v>=0&&v<1000001))))return {why:"malformed",key:"agreement_history_score"};
if(!f["agreement_status"].every(v=>["invalid","saturated","partially censored","censored","pending","complete","empty"].includes(v)))return {why:"malformed",key:"agreement_status"};
if(!(f["primitive_count"]===9))return {why:"cardinality",key:"primitive_count"};
if(!(f["meta_count"]===4))return {why:"cardinality",key:"meta_count"};
if(!(f["skill_count"]===3))return {why:"cardinality",key:"skill_count"};
if(!(f["demon_count"]===11))return {why:"cardinality",key:"demon_count"};
if(!(f["option_end_count"]===3))return {why:"cardinality",key:"option_end_count"};
if(!(f["history_bins"]===64))return {why:"cardinality",key:"history_bins"};
if(!(f["cycle_bins"]===16))return {why:"cardinality",key:"cycle_bins"};
if(!(f["exact_cycles"]===8))return {why:"cardinality",key:"exact_cycles"};
if(!(f["learner_count"]===51))return {why:"cardinality",key:"learner_count"};
if(!(f["control_criterion"]>=0&&f["control_criterion"]<2))return {why:"malformed",key:"control_criterion"};
if(!(f["action"]>=0&&f["action"]<9))return {why:"malformed",key:"action"};
if(!(f["facing"]>=0&&f["facing"]<4))return {why:"malformed",key:"facing"};
if(!((f["skill"]>=0&&f["skill"]<3)||(f["skill"]===255)))return {why:"malformed",key:"skill"};
if(!((f["option_start"]>=0&&f["option_start"]<3)||(f["option_start"]===255)))return {why:"malformed",key:"option_start"};
if(!((f["option_end_skill"]>=0&&f["option_end_skill"]<3)||(f["option_end_skill"]===255)))return {why:"malformed",key:"option_end_skill"};
if(!((f["option_end_reason"]>=0&&f["option_end_reason"]<3)||(f["option_end_reason"]===255)))return {why:"malformed",key:"option_end_reason"};
if(!((f["meta_action"]>=0&&f["meta_action"]<4)||(f["meta_action"]===255)))return {why:"malformed",key:"meta_action"};
if(!(f["ev"]>=0&&f["ev"]<64))return {why:"malformed",key:"ev"};
if(!(f["side"]>0))return {why:"malformed",key:"side"};
if(!(typeof f["run_id"]==='string'&&f["run_id"].length===16&&/^[0-9a-f]+$/.test(f["run_id"])))return {why:"malformed",key:"run_id"};
if(!(typeof f["audit_digest"]==='string'&&f["audit_digest"].length===16&&/^[0-9a-f]+$/.test(f["audit_digest"])))return {why:"malformed",key:"audit_digest"};
if(!(typeof f["source_sha256"]==='string'&&f["source_sha256"].length===64&&/^[0-9a-f]+$/.test(f["source_sha256"])))return {why:"malformed",key:"source_sha256"};
if(!(typeof f["build_sha256"]==='string'&&f["build_sha256"].length===64&&/^[0-9a-f]+$/.test(f["build_sha256"])))return {why:"malformed",key:"build_sha256"};
if(!["fresh","resumed","cleared"].includes(f["origin"]))return {why:"malformed",key:"origin"};
if(!["primitive","exploration_start","exploration_continuation","option"].includes(f["decision_source"]))return {why:"malformed",key:"decision_source"};
if(!["learned","hand_authored"].includes(f["subtask_policy"]))return {why:"malformed",key:"subtask_policy"};
if(!f["subtask_unit"].every(v=>(v===null||v<f["imprint_units"])))return {why:"malformed",key:"subtask_unit"};
if(!f["subtask_unit"].every(v=>(v===null||(v>=0&&v<2147483648))))return {why:"malformed",key:"subtask_unit"};
if(!(f["retire_unit"]===null||f["retire_unit"]<f["imprint_units"]))return {why:"malformed",key:"retire_unit"};
if(!(f["retire_step"]===null||f["retire_step"]<=f["lifetime_step"]))return {why:"malformed",key:"retire_step"};
if(!f["tiles"].every(v=>(v>=0&&v<8)))return {why:"malformed",key:"tiles"};
if(!f["tile_extra"].every(v=>(v>=0&&v<256)))return {why:"malformed",key:"tile_extra"};
return null;
}
const observerSnapshotFollows=(...p)=>((p[7]<p[0])||((p[0]===p[7])&&((p[9]===0)&&((p[8]<p[1])||((p[1]===p[8])&&((p[2]===1)||(((p[6]===1)&&(p[13]===0))||((p[10]<p[3])||((p[3]===p[10])&&((p[11]<p[4])||((p[4]===p[11])&&(p[12]<p[5]))))))))))));
const observerAfter=(...p)=>((p[3]<p[0])||((p[0]===p[3])&&((p[4]<p[1])||((p[1]===p[4])&&(p[5]<p[2])))));
const observerAgreementFollows=(...p)=>((p[3]<p[0])||((p[0]===p[3])&&((p[5]===0)&&((p[4]<p[1])||((p[1]===p[4])&&(p[2]===1))))));
const observerFollows=(...p)=>((p[3]<p[0])||((p[0]===p[3])&&((p[2]===1)&&((p[5]===0)&&(p[1]===(p[4]+1))))));
const observerWorldSuccessor=(...p)=>(p[0]===(p[1]+1));
function observerLog2(x){let k=0,p=2;while(p<=x){k++;p*=2;}return k;}
const observerCycleBucket=(x)=>(x<8?x:Math.min((8+observerLog2((Math.max(0,x-8)+1))),15));
const observerHistoryStart=(x)=>(x<1?0:(2**x));
const observerCycleFirst=(x)=>(x<8?(x+1):(8+(2**Math.max(0,x-8))));
const observerCycleLast=(x)=>(x<8?(x+1):(7+(2**(Math.max(0,x-8)+1))));
function observerEnvelope(f){return !!f&&typeof f==='object'&&!Array.isArray(f)&&Object.hasOwn(f,"run_id")&&(typeof f["run_id"]==='string'&&f["run_id"].length===16&&/^[0-9a-f]+$/.test(f["run_id"]))&&Object.hasOwn(f,"agent_epoch")&&(Number.isSafeInteger(f["agent_epoch"])&&f["agent_epoch"]>=0)&&Object.hasOwn(f,"timestamp_ms")&&(Number.isSafeInteger(f["timestamp_ms"])&&f["timestamp_ms"]>=0)&&Object.hasOwn(f,"lifetime_step")&&(Number.isSafeInteger(f["lifetime_step"])&&f["lifetime_step"]>=0)&&Object.hasOwn(f,"world_step")&&(Number.isSafeInteger(f["world_step"])&&f["world_step"]>=0);}
function observerControl(f){return !!f&&typeof f==='object'&&!Array.isArray(f)&&Object.hasOwn(f,"runId")&&(typeof f["runId"]==='string'&&f["runId"].length===16&&/^[0-9a-f]+$/.test(f["runId"]))&&Object.hasOwn(f,"agentEpoch")&&(Number.isSafeInteger(f["agentEpoch"])&&f["agentEpoch"]>=0)&&Object.hasOwn(f,"transition")&&["initialized","start_requested","stop_requested","clear_requested","core_started","core_stopped","restart_scheduled","archiving","cleared","failed"].includes(f["transition"])&&Object.hasOwn(f,"transitionReason")&&(typeof f["transitionReason"]==='string')&&Object.hasOwn(f,"reason")&&(typeof f["reason"]==='string')&&Object.hasOwn(f,"actual")&&["starting","running","stopping","clearing","stopped"].includes(f["actual"])&&Object.hasOwn(f,"desired")&&["running","stopped"].includes(f["desired"])&&Object.hasOwn(f,"seed")&&(Number.isSafeInteger(f["seed"])&&f["seed"]>=0)&&Object.hasOwn(f,"checkpointRefused")&&(typeof f["checkpointRefused"]==='boolean')&&Object.hasOwn(f,"clearDisabled")&&(f["clearDisabled"]===null||(typeof f["clearDisabled"]==='string'))&&Object.hasOwn(f,"terminalWarning")&&(f["terminalWarning"]===null||(typeof f["terminalWarning"]==='string'))&&Object.hasOwn(f,"tail")&&(Array.isArray(f["tail"])&&f["tail"].length<=6&&f["tail"].every(v=>(typeof v==='string')));}
function observerMap(f){return !!f&&typeof f==='object'&&!Array.isArray(f)&&Object.hasOwn(f,"runId")&&(typeof f["runId"]==='string'&&f["runId"].length===16&&/^[0-9a-f]+$/.test(f["runId"]))&&Object.hasOwn(f,"side")&&(Number.isSafeInteger(f["side"])&&f["side"]>=0)&&Object.hasOwn(f,"side")&&(f["side"]>0)&&Object.hasOwn(f,"side")&&(f["side"]>=0&&f["side"]<4097)&&Object.hasOwn(f,"seed")&&(Number.isSafeInteger(f["seed"])&&f["seed"]>=0)&&Object.hasOwn(f,"kinds")&&(typeof f["kinds"]==='string')&&Object.hasOwn(f,"partial")&&(typeof f["partial"]==='boolean');}
