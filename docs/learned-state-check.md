# How a submission on learned agent state is checked

> This page is the check that issue #295 names, the document by which a submission to that issue is read. The issue links one fixed revision of this page, and the linked revision governs how a submission made against that revision of the issue is read.

This is how a submission to [issue #295](https://github.com/rbeauchamp/acorn/issues/295) is read. It is the second revision of the check, and it is the same for every submission. Nothing here is a score. A submission is read under Acorn's [review protocol][p], which governs. This check says what a referee's report on this issue records: which of the frame's seven statements are proved, the status of each part, the referee's answers to eight questions that the frame cannot decide and to the questions kept from the first revision, and a reasoned placement on the range between prior art and discovery. "Learned agent state" in the heading is the name of the subject, from issue #17. No status or step of this check says that a state, a memory or a weight is learned; the one field that speaks of it, the answer to C4, is a judgement and is written as one.

## What a report can and cannot establish

A report can establish that a theorem is proved, that it is one of the seven statements in the frame's form, and that what a part claims is entailed by the theorems it names. It cannot establish what the frame does not certify: the eight questions of section C are answered by judgement, with reasons, and a referee can be wrong. It cannot establish that no computation was made beyond those the submission lists, or that no reading was taken beyond those it declares: the referee sees the pull request and not how it was produced. Neither a filled frame nor a complete submission is called a proof that the agent learned; what is established is the seven statements and the parts, and beside them stand the referee's recorded answers. No line of a report states as a fact that the agent, a memory, a state or a weight learned or is learned, except by naming a theorem of the pull request that states exactly that. Such a theorem is read by what its statement says with its definitions unfolded, and not by the name of a predicate: a predicate the author defines does not supply the word, and the report says in plain words what the statement establishes. An answer to C4 is written as the referee's judgement, with its reasons, and never as something established.

A report cannot establish that no earlier publication exists: a search is finite, and the same submission with the same search can be new or not depending on a paper the search did not reach. So a placement is a reasoned judgement on a recorded search. It is revised when earlier work is found, and it can be recorded as unresolved. The word discovery is not used of a submission while a plausible published predecessor is known and unread.

## Who reads, and what they are shown

1. The referee is assigned by the maintainers under the protocol's written rule: of another model family than every model that did the work, or a person, with no part in the work (it did not write it, advise on it or review it for the author), and neither taken nor passed over because the author asked. The assignment is written on the pull request.
2. The referee is shown the pull request at one named head commit: its diff, its description as it stood when read, the issue it names, and the repository at that commit. The maintainers hand the referee this material. The referee is not shown reasoning, notes, transcripts or drafts that led to the submission, and does not ask for them. The author addresses the referee only on the pull request, except on a finding that discloses a security vulnerability, which the referee reports, and the author answers, only by the private route the protocol names.
3. The referee may read any public source. The referee records the merge gate's result for that head as GitHub shows it on the pull request. The referee runs no experiment and no run of the agent.
4. A report counts only for the commit, the title and the description it read. After a push, or an edit of the title or description, the pull request has no clean report until it is read again. A submission that claims a discovery has two referees; neither sees the other's report before filing its own, both reports are kept, and where they differ each referee's reasons are recorded and neither report is edited to agree. A later revision of the issue or of this check gets a reading of its own.

## The report

The report is a comment on the pull request. A finding that discloses a security vulnerability is not written out there: it goes by the private route the protocol names. As the protocol asks of every report, it says what is claimed, what is established and what must change, and gives a verdict of accept, revise or reject. For this issue it has these fields:

- **Submission:** the pull request's address, the base commit, the head commit read, the description as read, and the revisions of the issue and of this check that were read.
- **Assignment:** who assigned the referee, what the referee is, and a statement that conditions 1 and 2 held.
- **Date.**
- **Gate:** GitHub's result for that head.
- **Read:** the files and theorems of the submission that were read in full, and any that were not.
- **Computations:** the submission's list of computations as read, and any computation on the agent or a learner that the submission shows signs of and the list does not account for.
- **Searched and read for prior art:** each search made, each source read with the passages relied on, and each source found and not read, with the routes tried.
- **Section A:** each of the seven statements, proved in the frame's form or not.
- **Section B:** the status of each part.
- **Section C:** the answer to each of the eight questions, with reasons.
- **Section D:** each answer to the questions kept from the first revision, with file and line, and its reasons.
- **Section E:** the placement, that it is unresolved, or that the submission is not placed and why, with reasons and citations.
- **Section F:** the disposition and the step.
- **Findings:** each with its location and what would correct it.
- **Differences** from the other report on the same submission, where there are two, added once both are posted.

## A. The seven statements

For each of (a) to (g) the referee records **proved in the frame's form** or **not proved**, with the theorem, its file and its line. These are obligations on the submission. The referee does not weigh them and does not accept a reason in place of one.

A statement is proved in the frame's form when the pull request holds a closed proof of the proposition that the frame gives for that statement, at the submission's own mechanism, family, goal and configuration: for every seed the agent accepts, from the cold start, with no hypothesis about the agent. It does not have to come out of a proof of all seven, so a partial result can be recorded statement by statement. Where a submission proves something else in its place, the referee records the statement as not proved and records what was proved instead, with every assumption stated: another agent, a state other than the cold start, some seeds, a premise about what the learners or the mechanism's memory hold, or a comparison other than the frame's.

The first revision of this check put the following to the reader as questions. The frame now states them as obligations, so they are no longer asked. What the frame leaves of each goes to the question named.

| First revision's question | Now stated by | What is left, and where it goes |
|---|---|---|
| 2. Is the information acquired through experience, and does its use matter | (a), from the cold start at every seed; (d) to (g) | Whether the use matters to a scored prediction and a needed action: part 1. Whether the memory was learned: question C4 |
| 5. Do the failure theorems distinguish the acquisition and use | (b) to (g), whose comparisons the frame fixes | Why the agent alone fails, and whether the failures share a world and a reason: C6 and C7 |
| 6. Is each shortcut excluded on a common task | (c) and (d), over every memoryless responder and rule, on the same worlds and goal | An agent with a hand-written memory: C2 |
| 7. Does the domain keep the distinctions after every hypothesis | No hypothesis about the agent is allowed; (b) to (g) each exhibit a world | Whether one kind of world shows them all: C6 |
| 8. Are the premises established where the claim is used | "No premise about the agent" | Nothing |
| 9. Do the quantifiers justify the uniformity claimed | The frame's quantifiers: every seed, every world; the rule or schedule chosen knowing the seed and before the world | Nothing |
| 11. Is the achievement specified independently of storage, and compared on the same terms | The goal reads the world, its states, the agent's actions and its stored predictions and not the inside of the agent; the comparisons are fixed | Whether the goal grades the agent against itself: C1 |
| 13, second half. Are the premises about the agent derived | "No premise about the agent" | Nothing |

## B. The parts, each with its own status

For each part the issue asks for, the referee records two things separately: whether it is **present**, with file and line, and whether what it claims is **established**, **not established**, **open** (the submission itself leaves it open) or **not applicable, with the reason**. Presence is not soundness, and one part's status does not carry to another. A reason given in place of a theorem is judged like any other claim; it does not establish the theorem it replaces.

| Part | Established when |
|---|---|
| 1. The information to be acquired, and three clauses of #17's statement | The information the assembled agent has to acquire and use is named; theorems show that the mechanism's memory is built online from the stream, without back-propagation through time or stored trajectories; and one theorem entails feeding in the issue's meaning. Whether the mechanism keeps a record of experience is question D2. The status is written "part 1: the three clauses established". It is never written as #17's statement established or as a state being learned: whether the memory is learned is the answer to C4, which is a judgement |
| 2. The seven statements | All seven are proved in the frame's form under section A |
| 3. The mechanism, in the assembled agent | The statements the submission claims, (a) among them, are the frame's own propositions; the pull request changes nothing of the fixed agent or of the owner's trusted base; and the gate passes on the head |
| 4. The setting and affordability | For each clause of the admission standard on the setting and on affordability, read of the mechanism and of the assembled agent's whole step: a theorem, with its unit of work or memory, the quantities that vary, and whether it bounds the mechanism or the whole step. A clause without one is open |
| 5. The account of prior art | The closest relevant published work is cited with locators, and each substantive difference is stated |
| 6. Claims and their support | Each claim about what the agent does is entailed by the theorem it names, hypotheses included; argued, attributed and open statements are labelled |
| 7. The list of computations | The list is present; each entry that stepped the agent or a learner names a theorem of the pull request that states its value, or is declared a run with its authorization; and the referee finds no sign of a computation the list does not account for |
| 8. The readings taken | The list is present, or the sentence that every item is claimed under the issue's words; and the referee finds no item claimed under a reading the list does not give. An entry does not establish the item it concerns: that item is judged by the issue's words |

## C. The referee's eight questions

The frame admits each of the following; its seven statements do not refuse them. The referee answers each in writing, with file and line and with reasons. An answer is the referee's judgement on what the submission shows.

1. **A goal that grades the agent against itself.** It is proved that whenever any goal has a result that fills the frame, so does the goal "the run is exactly this agent's own run", on the same worlds. So, of the goal that grades the agent against itself, the seven statements say this: for each compared run and each seed, there is a world of the family in which that run is not the agent's run at any seed. They do not say that the runs differ in every world. Such a separation of runs holds exactly when some goal fills the frame with this mechanism and these worlds, and the frame admits the goal that grades the agent against itself. It does not justify the goal a submission poses: that goal must itself accept the agent's runs and reject the compared ones. *Question:* could this goal be posed to an agent the contributor has never seen? Is it stated by what the world rewards and what happens next in the world, and not by the agent's own exact outputs?
2. **A goal that asks for nothing learned.** Statement (c) refuses every goal that a responder with no memory satisfies across the family. It cannot refuse a goal that a hand-written agent with a memory satisfies. *Question:* what is the simplest agent, of any kind, that satisfies this goal across the family, and does it need to adapt to the world?
3. **Prior knowledge in the mechanism, the worlds or the goal.** The mechanism may be a table prepared in advance from knowledge of the worlds. The worlds may hand out answers. The goal may refer to the agent's code. *Question:* what did the author know about the family when writing the mechanism, and would the result survive a family the author had not seen?
4. **A memory written by a hand-written rule.** The frame certifies that Acorn's learners' stores were needed relative to fixed ones, and that the mechanism holds something of the stream. It does not certify that the memory was learned. *Question:* which part of the mechanism changes with experience by a learning rule, and what is lost if that part is frozen?
5. **Worlds the agent never meets where it is run.** The family may consist of worlds whose observations Acorn's own grid world never produces. *Question:* do the family's observations occur in the worlds Acorn is run in, and what does the result say about those?
6. **Statements witnessed in separate worlds, and padding.** The world that shows (b) may have nothing to do with the worlds that show (e) and (f), and the family may contain worlds where the goal asks nothing. Nothing requires a failure under (e) to be a failure of prediction, or under (f) a failure of action. *Question:* is there one kind of world in which the base agent fails, a memory is needed and both learners are needed, for the same reason?
7. **Why Acorn's agent alone fails.** *Question:* would it succeed if the missing information were put in its observation?
8. **That the program Acorn runs is the assembled agent**, and that an observation has room for the mechanism's words. *Question:* does the binary's step do exactly this, on observations that are not full, where only part of the list fits, and where a word uses a channel the agent keeps for its own predictions?

An answer is a finding when it shows that the result is less than the submission claims. It is also a finding when the submission is one of the things the issue says does not stand in for one and is presented as more than it then is. Saying so openly does not make it more: such a pull request can be read as what it is, a partial result, a negative result or a filled frame that the issue excludes, and can have a clean report as that, and it stays below step 6 and is never complete. The report is not clean while a finding is open. An answer that shows neither is recorded with the result, as a judgement and under the referee's name, and no answer makes a result a proof that the agent learned.

For this issue the answer to C4 decides one more thing. Where the referee judges that nothing in the mechanism changes with experience by a learning rule, in the sense the issue gives under "How a submission is judged", the submission goes no higher than step 5 and is not complete. The judgement itself fills no frame and reaches no step: the record is still the statements proved and the step they reach, and the words filled frame are used only where all seven statements are proved under section A. The referee writes the reasons: which parts of the mechanism were considered and why those; whether experience changes how the mechanism keeps or offers what it remembers, or only what it remembers; whether anything of what was experienced enters through each part; and whether the goal's satisfaction, as statement (a) has it, is lost when the part is held at its starting value. A referee who cannot tell says so, with reasons; the question is then unresolved, and the submission is not at step 6 until it is answered. This is a judgement and not a theorem.

These questions take over what the first revision asked in its questions 1 (whether the goal is stated independently of the submitted program: C1), 3 (whether the achievement comes from the problem, the criterion or hand-authored machinery: C2, C3 and C4), 4 (whether membership of the family assumes or selects for the achievement: C3 and C6), 10 (whether the assumptions about information and timing hold for every execution: C5 and C8), 12 (whether the result reaches the executed entry point: C8) and the first half of 13 (which assumptions about the environment delimit the claim: C5).

## D. Questions kept from the first revision

Each is answered **no defect found**, **defect shown**, **unresolved** or **not applicable, with the reason**, with file and line and the reasons. A referee who answers no defect found says what was checked. The word established is kept for a part and for what a theorem entails. Unresolved is an honest answer and is recorded as such: an unresolved question about a required theorem keeps the part it belongs to from being established, and an unresolved question about earlier work keeps a placement from being unqualified. Neither erases a theorem that is sound. The number each question had in the first revision is given in brackets.

1. [14] Does any proof relied on for the result go beyond the project's approved trust base?
2. [15] Does the mechanism, or any other part of the submission, store experience or replay it, contrary to the setting of parts 1 and 4 and to the mission contract's third contract? To store experience is to keep a record of past observations, actions and rewards as they arrived; what the agent has learned is not such a record. A record kept in another encoding, or divided among several structures, is still a record. The referee names what is kept, in what form, and how it is used.
3. [16] For each clause of part 4, what is proved, for which resources and over which varying quantities?
4. [17] Does any conclusion about learning, or the choice of the goal, the family or a bound, rest on a run or a measurement? A proved witness establishes what it states. A doubt about how a value was arrived at that the referee cannot settle from the submission and its list of computations is recorded as unresolved.
5. [18] Does the pull request put a hand-authored bias on the path to an action otherwise than through its mechanism's words? The mechanism itself is not a departure of the learned-only register and earns no credit as learning: it is read under C3 and C4, as the issue says under "The frame" and [Acorn's own text][m] says. Anything else the pull request puts on that path is read by the learned-only binding at the commit named. That a bias is declared does not answer this question: a declared departure is no evidence of learning, and a new departure is not part of a submission.
6. [19] Which published methods found in the referee's recorded search meet the same problem under the same assumptions about information, setting and resources? The answer is a witness, none found in the search recorded, or unresolved. "None found in the search recorded" is an answer to this question as it is written, and is not a claim that none exists.
7. [20] Which parts of the submission's mechanism are equivalent to published methods, including under a change of representation, and are they attributed accurately? The referee checks each attribution against the source itself.
8. [21] Is the mechanism a combination of published methods, and if so what did combining them take beyond applying each? Is what is new a proof of an algorithm that is not new? Is any statement or part carried over from the proofs of an earlier result, and from which?
9. [22] For a pull request that proves a goal cannot be met: exactly what claim is ruled out, is it a claim about Acorn's agent, can any agent meet the goal, and what in the argument goes beyond bounds already cited? A goal that no agent can meet rules out nothing about Acorn's agent.

## E. Placement between prior art and discovery

[Prior art and discovery](prior-art-review.md#prior-art-and-discovery) states the range and its four questions. The referee answers them in writing, with citations to the submission's code and to published work, and gives a placement by extent on that range.

- The referee identifies what the submission contributes to the result it proves, and the strongest alternative account of that contribution from prior art, which may involve several earlier works and not one.
- A difference that the result does not need earns no credit, and neither does a statement or a part carried over from the proofs of an earlier result. A new proof of a published algorithm does not make the algorithm new. A combination of published methods is credited with what combining them took.
- That an earlier method meets the same goal, and that the submission's mechanism was already published, are two different findings. An earlier method that meets the goal only under other assumptions or at another cost is recorded with those assumptions, and the submission is placed by what it adds.
- Where the evidence does not distinguish two accounts, the referee records that limit, and the placement is **unresolved**.
- A placement toward discovery is a claim of discovery, and is made only on two referees' reports under the protocol.
- Only a submission that fills the frame, whose parts are established and which the issue does not exclude is placed. A partial result is not placed: the referee records which of (a) to (g) it proved and what else was and was not established.

A placement is the referee's judgement on the evidence recorded. It is not a certificate of priority, and it is revised when an earlier work is found.

## F. Dispositions, and how far a submission got

Each of these is its own disposition. None is by itself a discovery.

- **A faithful implementation of published work, with or without a cited correction.** It can be complete. It is recorded as prior art put to use, with its proofs kept.
- **A different mechanism for a goal that an earlier solver can meet.** The earlier solver is recorded under question D6 with its assumptions and cost. If the submission fills the frame and its parts are established, it is placed by its extent under section E.
- **A theorem with a premise about the agent.** This is not a result read on its scope. It is a partial result that has proved none of the statements its premise conditions, and it is recorded so, with the premise stated. That a state satisfying the premise can be constructed does not change this: only a theorem that reaches the premise from the cold start, for every seed the agent accepts, does.
- **Conditions on the worlds.** A result whose family is defined by what its worlds provide is read on that family. The conditions are the family's definition, and questions C3, C5 and C6 ask what they hand to the agent.
- **A proof that a goal cannot be met.** A negative result about the exact claim it rules out. It does not fill the frame, and statement (a) is recorded as not proved. Whether it is about Acorn's agent, whether any agent can meet the goal, and its contribution beyond known bounds are judged under question D9.
- **A changed goal.** Where the claim proved differs from the claim first posed, the submission states both and the difference, and the report is of the claim proved. A changed goal changes nothing about the frame: the claim proved is read against the seven statements, and one that proves fewer is partial.

A submission that does not fill the frame is partial, and it is recorded by which of (a) to (g) it proved, with any assumption stated. The step below is a summary of that record and never replaces it.

These steps are stages of a submission's record. They are not steps of the agent's run. Step 0 is the record when step 1 is not reached. From step 1 on, a step is reached when its own conditions hold together with those of every step from 1 up to it, and the referee records the highest step reached. A reason in place of a theorem, or a proof for some worlds of the family where the statement says every world, does not reach a step.

| Step | Reached when | What it says, and what it does not |
|---|---|---|
| 0 | The change does not build | Nothing |
| 1 | The change builds | Nothing about the task |
| 2 | A mechanism, a family of worlds and a goal are stated in the frame's form, with the fixed agent unchanged, and the information to be acquired is named | That a task is posed. No theorem is credited by this step. It does not say that any agent can meet the task, or that the task needs the past |
| 3 | Statements (a) and (c) are both proved in the frame's form. An agent built by hand does not count at this step: that some agent defined in Lean meets the goal does not reach it, and neither does the assembled agent started from a state that the proof library constructs, a proof for some seeds, or a proof under a premise about what the agent's learners or the mechanism's memory already hold | That the assembled agent's run, from its cold start, at every seed, in every world of the family, satisfies a goal that no memoryless responder satisfies across the family. It does not say that the mechanism plays any part: Acorn's agent alone may satisfy the same goal |
| 4 | Statements (b), (d), (e), (f) and (g) are proved as well: the frame is filled | The necessary conditions of "What filling the frame does not show". It does not say that the agent learned, or that the mechanism's memory was learned |
| 5 | Part 1's three clauses are established, and every clause of part 4 is established, none left open | That a prediction learner's weight and a control learner's weight, each changed from its cold-start value during the run on a feature that only the mechanism's words have made active, each decide an output on which the goal turns, within the setting. It does not say that anything was learned, and it does not answer the eight questions. A submission whose mechanism the referee judges to hold nothing that changes by a learning rule goes no higher than this step; that judgement reaches no step by itself |
| 6 | Every part is established, the submission is none of the things the issue says does not stand in for one, the referee has answered C4 and has not judged that nothing in the mechanism changes by a learning rule, no finding is open, and the report is clean on the commit that is to merge, both reports for a claim of discovery | That an assigned referee found the claims supported. A placement may still be unresolved |
| 7 | Complete: the pull request has merged, with the gate's pass on the head commit that merged | The outcome of the protocol |

A statement proved without the ones a step requires is in the record and reaches no step by itself: without (a) and (c) together a submission is at step 2 at most, whatever else it proves and in whatever order. Statements (b) to (g) can all be proved of a task that no agent could meet, and (a) of a goal that every run satisfies, so proved without (a), or (a) without (c), they are no evidence about the mechanism or about Acorn's learners. A pull request whose whole claim is such a result, or a proof that a goal cannot be met, is at step 2 at most.

Steps record what is proved, not how much of it is new. A submission may carry its statements over from the proofs of an earlier result, for instance the same mechanism and worlds under a goal that accepts the earlier runs' own traces, which the theorem cited in C1 allows. It is then at the step those proofs reach, and the step is no evidence of new work: the report names the earlier result and what is carried over from it (question D8), section E gives what is carried over no credit, and question C1 is answered of the new goal.

A clean report can be given at any step from 1 on. It says that the pull request claims no more than it proves. It does not raise the step: a partial result with a clean report, merged or not, is a partial result at its step.

The step says what was established. It is not a score. An author states the step a submission claims and which of (a) to (g) it claims to prove, each with its theorem; the referee records the step. No author's statement reaches step 6 or 7, which are the protocol's outcome. Whether a complete submission is prior art put to use or a discovery is its placement, whether it is admitted into Acorn is the admission standard's question, and whether it closes the issue is the owner's decision.

## What decides nothing

A run of the agent, a score, a benchmark, a count of theorems or of lines, the time a submission took, the author's own statement, the author's own reviewer, and the gate's pass taken alone.

[m]: learned-only-binding.md
[p]: ../CONTRIBUTING.md#review-protocol
