# The frame of a learned-state result, in plain words

This restates, without Lean, what the frame says. The frame is the Lean of `lean/AcornVerif/Targets/LearnedState.lean` and `lean/AcornVerif/Targets/LearnedStateAcorn.lean`.

**The owner's decisions.** On 2026-11-20 the owner confirmed this page as written and made the two choices it puts. On the question at its head, the agent stays fixed for a submission and a learner change lands separately, first (option 1 below). And the frame is adopted as a set of necessary conditions, with a referee. Everything below this paragraph is the page as the owner confirmed it: where it speaks of a choice still to be made or of a confirmation still to come, those are the ones recorded here. A change to what the frame requires, allows or rules out goes back to the owner first.

It is for the owner to confirm or correct before anything is built on the frame. The frame has been attacked twice by a model that had not seen its reasoning. The first attack broke an earlier design of the frame, called revision 1 below. The second found no way to complete the present frame on Acorn's agent without first proving real facts about Acorn's learners, and showed exactly what a completed proof would and would not mean; one statement was added after it.

**Read this first.** A proof in this frame is a set of necessary conditions. It is not a certificate that an agent learned to do a task.

- **What it certifies.** That the run of Acorn's agent with the submitted mechanism satisfies a statement the contributor wrote, from a cold start, at every seed, in every world of a family the contributor chose; that no responder without a memory of the past satisfies that statement across the family; and that five other named agents do not either: Acorn's agent alone, Acorn's agent fed by a memoryless rule, and Acorn's agent with the mechanism but with its prediction learners' store, its control learners' store, or both, overwritten by stores fixed in advance. "Needed" always means: needed relative to those named comparisons.
- **What it does not certify.** That the statement is a task anyone would pose. That the mechanism's memory was learned and not written by hand. That nothing was known in advance by the mechanism, the worlds or the goal. That the worlds resemble the ones Acorn runs in. That the same world shows all the failures. A referee has to read those; part 6 lists them with the question for each.

It is not known whether any such proof exists for Acorn's agent as it stands. The next section says why, and what the owner has to choose.

## The question to settle first: may a submission change Acorn's learners?

**What the frame does today.** Under the frame as written, Acorn's agent is fixed: its learners, the way it chooses actions and the way it explores. A submission adds one thing only, a state mechanism that hands the agent extra sensor words. Everything the agent does with those words is done by its present learners.

**What follows.** If the present learners cannot make use of what a mechanism hands them, then no submission can be complete, however good its mechanism is. The statements of part 3 would have no proof, and the reason would lie in the fixed agent and not in any submission.

**Whether they can is open.** Acorn's record carries it as an open question, issue 296: whether the standard agent's learners can make quick use of one added state feature, to be settled by a theorem about the executed agent in one direction or the other. Nobody has proved either. Until it is settled, it is unknown whether any complete result exists for the agent as it stands. The issue is about one added feature, and it says itself that an answer for one says nothing of several, so even its answer may leave part of this open. Nothing in this document, and nothing proved for it, bears on that: the small example of part 7 uses its own small learners, not Acorn's. The second attack looked for a complete proof on Acorn's agent and did not find one; it records the first proof about Acorn's learners at every seed as the cost nobody has paid.

**So there are two ways to let a contributor who needs a different learner proceed. The choice is the owner's.**

*Option 1: the agent stays fixed for a submission, and a learner change lands separately, first.*

- What the contributor does: makes the change to the learners as its own pull request to the fixed agent. That pull request states and proves what the change is for, on its own terms; this frame says nothing about it. It passes the same independent, adversarial review and the same gate as any other contribution, and it merges only on the owner's word. The owner then fixes the agent again at the new commit. Only after that does a learned-state submission build a mechanism on the changed agent.
- What it does to the comparison: statement (b) compares against "Acorn's agent alone". After a learner change lands, that agent is the changed one. So a later result shows that the mechanism was needed given the new learners. It does not show anything against the agent as it stood when issue 295 was published, and whatever the learner change itself gained is credited to that change and to its own proofs, not to the learned-state result.
- What it costs: two steps where issue 295 as published has one. Issue 295 asks a contributor to change how the agent learns; under this option a submission to it may not, so the option is narrower than the issue and the issue would have to say so. Each learner change also moves the fixed agent, so theorems already proved about the earlier agent have to be proved again for the new one.
- What it needs in order to be acceptable: a stated route by which learner changes land. A frame that fixes the learners and offers no way to change them could block all progress, since it may be that no mechanism can succeed with the present learners. The route proposed here is the one in the first bullet. The owner may set a different route; there has to be one.
- What it leaves uncertified: the questions of part 6, which go to a referee; the merit of each learner change, which its own pull request has to carry; and whether any complete result exists at all.

*Option 2: a submission may change the learners itself.*

- What the contributor does: changes the learners and adds its state mechanism in one submission, as issue 295 is published.
- What it does to the frame: statements (d) to (g) lose their force. They work by overwriting the real learners' stores in the real step. If the submission writes the step, it also writes what happens when a store is overwritten, and it can write that so the statements hold for an agent that learns nothing. That is how revision 1 was broken (part 9). What still holds by its form is (a), (c), and (b) against a kept copy of the earlier agent.
- What it costs: completeness then rests on the referee for what the frame was meant to carry: that learning was needed at all, that a memory in the agent was needed, and all of part 6. The kept copy of the earlier agent is a duplicate of a large part of the code.
- What it leaves uncertified: the above, and also whether any complete result exists.

**Recommendation, with what it does not settle.** Option 1, together with the stated route for learner changes. It keeps the parts of the frame that are true by construction. It leaves three things uncertified: the questions of part 6, the merit of learner changes, and whether the present or any later fixed agent admits a complete result. Option 2 leaves more uncertified and matches the issue as published. Neither option removes the need for a referee.

## 1. What the frame is for

Acorn asks contributors to give its agent state that it builds from its own stream and then uses in its predictions and its control. The frame fixes how such a result is stated, so that a proof is about Acorn's own learners, started from Acorn's standard cold state.

A submission is **complete** only if it proves the seven statements of part 3 in the form the frame fixes. Any other submission is **partial**, and is recorded by which of the seven it proved. A theorem that assumes one of the seven, or assumes that a complete result exists, is a partial result until someone proves what it assumes.

## 2. What is fixed, and what the contributor supplies

**Fixed, and not changed by a submission:**

- Acorn's agent as it stands: its standard cold state at each seed, its whole step, its learners, how it chooses actions, how it explores.
- How anything new reaches it: a mechanism offers a list of extra sensor words with each observation. The list is added to the observation's own words only if the observation has room for all of it and none of the words uses a channel the agent keeps for its own predictions; otherwise the whole list is dropped. An observation that is already full takes nothing. Words that are added are coded like the world's own words; two words can fall on the same feature, and nothing in the frame says that an added word gives a new feature or that any learner comes to use it.
- A mechanism cannot write the reward, the other parts of the observation, or the agent's internals. It can still change what the world shows later, because what it hands over can change the agent's actions.
- What "the prediction learners' store" and "the control learners' store" are: the whole records of the prediction learners, and of the primitive controller and the meta controller. Other learning in the agent (option policies and models, the feature bank) is not part of either store.
- What the replacements of part 3 do.

**Supplied by the contributor:**

- **A state mechanism**: a memory with its own starting value at each seed, a rule for updating it from each observation and from the agent's own outputs, and a rule for which extra words it offers. It may be any function at all. It may contain learning rules, a table prepared in advance, or knowledge of the task.
- **A family of worlds and a goal.** The goal is any statement about a world of the family, that world's states, the agent's actions and the predictions the agent stores at each step, over the whole endless run. It is given which world it is judging. It cannot read the seed of the run or the inside of the agent, but it may be written with full knowledge of the agent's code, and it may judge only a few moments.
- Which standard configuration of the agent is used, apart from the seed.

The agent a result is about is Acorn's agent run on observations extended by the mechanism. Call it the assembled agent.

## 3. What a complete result must prove

Seven statements, each for every seed the agent accepts. The finished proof may assume nothing about the agent.

**(a) The assembled agent's run satisfies the goal**, from its cold start, in every world of the family.

**(b) Acorn's agent alone does not**, in at least one world of the family.

**(c) The task needs the past.** Take any responder that has no memory: at each step it emits an action and a list of prediction words chosen by a rule that reads only the clock and what the world delivers at that step. In at least one world of the family, its run does not satisfy the goal. This is a statement about the worlds and the goal only; it does not mention Acorn's agent. It covers every such responder, whether or not its prediction words are of the kind Acorn's agent can emit.

**(d) A memory in the agent is needed.** Take away the mechanism and offer the agent, in its place, extra words chosen by any rule that reads only the clock and what the world delivers at the current step. In at least one world of the family, that run does not satisfy the goal.

**(e) The prediction learners' store is needed.** Keep the mechanism. Before every step, overwrite the prediction learners' store with one fixed in advance: any schedule of stores over time. In at least one world of the family, that run does not satisfy the goal.

**(f) The control learners' store is needed.** The same, overwriting the control learners' store.

**(g) Both together.** The same, overwriting both stores.

In (c) to (g) the rule or schedule is chosen knowing the seed and before the world is chosen. It can be any function at all. In (e) to (g) the learners still run inside each step, and everything outside the named stores carries on as before.

On Acorn, (b) follows from (d): offering no words is one of the rules in (d), and Acorn's agent offered no words is Acorn's agent. This is proved. Both are kept, because (b) is the comparison the owner asked for by name and because for an agent other than Acorn's it need not follow.

Illustrations. None of these is a rule; each depends on the rest of the task.

- (c) fails for a goal with an alternative that a constant answer satisfies, and for a goal that can be satisfied by copying something from the current step. Both are proved refused (the first on the small example, the second in general).
- (g) fails where the remembered thing is itself the answer and a fixed store that passes it through satisfies the goal. Proved on the small example. On Acorn it would have to be a store Acorn's readout can actually realize.
- (d) fails for a mechanism that offers the same words whatever it remembers, or follows only a clock, when (a) holds.
- A proof for one seed, or from a state other than the cold start, is not (a). It does not show (a) false either.
- A family in which the same remembered cue calls for opposite answers in different worlds is the kind of family in which (e) to (g) can hold. It does not make them hold: the clock, other features, and what the world does next can still tell the worlds apart.

## 4. What follows from the seven statements

Proved for every complete result:

- What the mechanism offers during the run is not determined by the clock and what the world delivers at the current step.
- What the prediction learners hold during the run is not the same schedule in every world of the family. The same is true of the control learners.
- The family has at least two worlds. The goal is satisfied by some run and not satisfied by another.
- No agent whose output depends only on the current step satisfies the goal across the family.

## 5. What the seven statements do not say

- They do not say that every world of the family requires learning or memory. (a) is for every world; (b) to (g) each need only one world, and it may be a different world for each statement and for each rule or schedule.
- They do not say the agent "achieves" anything. They say its run satisfies a statement the contributor wrote.
- They do not say that what the agent learned is what the goal asks for.
- "Needed" is relative to the named comparisons. Nothing is said about all possible controllers, all possible predictors, or agents with a hand-written memory.
- (g) overwrites the two named stores only. It does not say the agent then learns nothing.
- They do not say the agent started from nothing. Acorn's agent starts from its standard cold state. The mechanism, the worlds and the goal may hold anything their author knew.

## 6. What the frame admits, and the referee's question for each

No statement of this kind can refuse these. Items 1 and 2 are theorems.

1. **A goal that grades the agent against itself.** Proved: whenever any goal has a complete result, so does the goal "the run is exactly this agent's own run", on the same worlds. So the seven statements say that the agent's run differs from every compared run, and nothing more about the goal. *Question:* could this goal be posed to an agent the contributor has never seen? Is it stated by what the world rewards and what happens next in the world, and not by the agent's own exact outputs?
2. **A goal that asks for nothing learned.** The second attack proved, on Acorn's real step and for the six statements the frame then had, that any complete result can be turned into one whose goal a much simpler agent satisfies: a constant answer, or a copy of the current reward. Statement (c) was added for this and refuses every case in which the simpler agent has no memory. It cannot refuse a goal that a hand-written agent with a memory satisfies. *Question:* what is the simplest agent, of any kind, that satisfies this goal across the family, and does it need to adapt to the world?
3. **Prior knowledge in the mechanism, the worlds or the goal.** The mechanism may be a finite table prepared in advance from knowledge of the worlds; the attack argues that if any complete result exists, one exists with such a table. The worlds may hand out answers. The goal may refer to the agent's code. *Question:* what did the author know about the family when writing the mechanism, and would the result survive a family the author had not seen?
4. **A memory written by a hand-written rule.** The frame certifies that Acorn's learners' stores were needed relative to fixed ones, and that the mechanism holds something of the stream. It does not certify that the memory was learned. *Question:* which part of the mechanism changes with experience by a learning rule, and what is lost if that part is frozen?
5. **Worlds the agent never meets where it is run.** The family may consist of worlds whose observations Acorn's own grid world never produces. *Question:* do the family's observations occur in the worlds Acorn is run in, and what does the result say about those?
6. **Statements witnessed in separate worlds, and padding.** The world that shows (b) may have nothing to do with the worlds that show (e) and (f), and the family may contain worlds where the goal asks nothing. Nothing requires a failure under (e) to be a failure of prediction, or under (f) a failure of action. *Question:* is there one kind of world in which the base agent fails, a memory is needed and both learners are needed, for the same reason?
7. **Why Acorn's agent alone fails.** *Question:* would it succeed if the missing information were put in its observation?
8. **That the program Acorn runs is the assembled agent**, and that an observation has room for the mechanism's words (see part 8). *Question:* does the binary's step do exactly this, on observations that are not full?

## 7. What the small example shows, and what it does not

- The small world shows a cue, then a blank step at which the agent must act and forecast. Whether the action paid, and an echo, arrive with the next cue. Two hidden settings of each world decide which action pays after which cue and which echo follows which cue.
- The small base agent has two learners that record, from the feedback of earlier trials, which action paid and which echo followed, for each key it is handed. Alone it is handed no key. The small mechanism keeps the last cue and hands it over as the key. That mechanism is a hand-written rule; item 4 of part 6 applies to it.
- Proved: all seven statements. Also proved: with an alternative added to the goal that a constant answer satisfies, there is no complete result; where the hidden settings are fixed so that the cue is itself the answer, there is none; and the same small agent has a complete result for the goal that grades it against itself, which is item 1 of part 6 on an example.

**What this establishes:** the seven statements can be met together, and each is false of a named cheap kind of result.

**What it does not establish:** that Acorn's agent can meet them with any mechanism. Nothing here attempts that, and whether it can is open (see "The question to settle first").

## 8. Conditions on landing the frame

- **Room for the mechanism's words.** Acorn's grid observation has a fixed maximum number of words, and an observation at that maximum drops every list a mechanism offers. Grid observations are not always at the maximum, but they can be. Before the frame is used, the agent's interface has to leave room for a mechanism's words. That is a change to the fixed agent, so it is the owner's.
- **The fixed agent has to be pinned**, so that a submission cannot edit it, and the program has to run the assembled agent. Both are the owner's side.
- Under the frame as written, a contributor may not change Acorn's learners within a submission. Whether that stands is the fork at the head of this document.

## 9. What changed since revision 1, and why

The first attack produced a submission that satisfied revision 1 while emitting the same action and the same predictions in every world. It used three freedoms revision 1 gave the contributor.

| Freedom in revision 1 | What it allowed | Now |
|---|---|---|
| The contributor described what the step would do with replaced outputs | A description that misbehaves only on replaced outputs | The step is fixed. The replacements overwrite the real stores of the real agent. |
| The contributor chose what a replacing rule could see | Hiding the remembered cue from the rule | No such choice exists. |
| The contributor chose the goal | A goal that asks nothing, or that grades the agent against itself | Still the contributor's. Statement (c) refuses goals a memoryless responder satisfies. The rest is part 6. |

Three statements were added to the four the owner asked for: (c) after the second attack; (d), so that a mechanism with no memory of the stream cannot pass; and (g), so that a goal which only asks the two kinds of output to agree cannot pass.

## 10. Choices made on the owner's behalf

1. The frame as written fixes the agent's step, so that a submission only adds a mechanism. Whether a submission may instead change the learners is the owner's choice and is not decided here.
2. Statements (c), (d) and (g) are added to the four the owner asked for. The designing agent proposed them and the agent supervising Acorn's research decided to keep them; the owner may change that.
3. The stores are the prediction learners' and the two controllers'. Other learning in the agent is not overwritten, which makes (e) to (g) harder to satisfy, never easier.
4. A goal reads the world it is judging, that world's states, the agent's actions and its stored predictions.
5. A partial result is recorded by which of (a) to (g) it proved, with any assumption stated. It is not called complete, is not said to solve the issue or to show that the agent acquired state, and is not placed between prior art and discovery.
6. A complete result is necessary and not sufficient for a learned-state result: it goes to a referee with the questions of part 6. This is the position the agent supervising Acorn's research has taken to the owner.
