<!-- Before the first section, say in a few sentences what this change does and why, for a reader who has seen none of the discussion that led to it. Give each resolved mission or issue its own closing keyword line (`Closes #<id>.`), and when an AI agent or model contributed, credit both the human contributor and the agent or model. -->

<!-- This description becomes the change's commit message when it is merged, so write it as a record of the change as it stands, not a history of its review. Keep the four sections below in every pull request, with their headings unchanged and in this order, and keep each up to date as the change evolves. Never leave a section empty: where it does not apply, write one line that says so and why. Write each paragraph and each list item on a single line. A section may hold `##` subsections, for example for what was measured or for the outside behaviour the change relies on. -->

# Mission accounting

<!-- What the change must keep true, and how that is known. Fill each line below; write "none" where a line does not apply, and say why. For a mission pull request, name the mission issue (`Closes #<id>.`), confirm that its frozen theorem or decision contract is unchanged and only the mission's listed files are touched, credit the human contributor and any AI agent or model, and paste the result of running `./scripts/gate.sh` on the exact pull request head. -->

- Mission and credit: <!-- for a mission pull request, `Closes #<id>.`, the frozen theorem or contract established, the touched files, and credit for the human contributor and any AI agent or model; write "none (not a mission pull request)" otherwise -->
- Gate result: <!-- the `./scripts/gate.sh` result on the exact pull request head (paste the `gate:` summary lines showing `./scripts/verify.sh build-executing`, `./scripts/verify.sh` and `./scripts/lean.sh lint` passing, or include in a fenced block below) -->
- Mission properties: <!-- the properties of the project's purpose that this change depends on or affects, each stated so a reader could tell when it fails -->
- Formal claims: <!-- the proofs, types and checks in the code that express those properties, each named so a reader can find it; say so plainly when the change adds none -->
- Trusted base: <!-- the assumptions those claims rest on without proof, such as how a compiler, an operating system or an outside service behaves -->
- Where proof would shrink it: <!-- which of those assumptions a proof could remove, and what that proof would need -->
- Specification consequences: <!-- for each specification the change adds or changes, what it requires, what it allows, what it rules out and what it leaves unsaid, in plain words with an example -->

# Decisions

<!-- One line for each choice the author made where another option was reasonable: the choice and its reason, so a later reader can see it and reverse it. -->

# Accepted risk

<!-- One line for each known way the change could fall short that it does not guard against, including review findings judged not to need a fix: the risk, and why accepting it is reasonable (its failure is cheap and easy to undo, or a guard would cost more than it saves). Write "None known." when there is none. -->

# Root cause (defect fixes only)

<!-- For a change that fixes a defect: the property that failed; the proof, type or check that should have made the failure impossible; the assumption the reasoning relied on in its place; the whole class of defects of that kind, how it was searched for, and each place found with what was done about it; and why the project let the defect arise unnoticed, followed link by link to something that can be changed, with that change. For any other change, write "Not a defect fix." -->
