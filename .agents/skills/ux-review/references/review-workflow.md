# UX review prompts

Use the questions relevant to the changed viewer behavior; one reviewer can
cover them together. Inspect the rendered build and DOM, not a remembered image.
A missing relevant state is a limitation to disclose, not an assumed pass.

| Prompt | Audience | Question |
|---|---|---|
| First impression | Sutton | Above the fold, cold: what is this, what does it optimise, how is it doing — and is the subject (knowledge, options, step sizes) shown, or only the setting? |
| Honesty | Javed | For every figure: what is it, over what window, computed where; could a careful experimentalist read it as a claim the stream does not support? |
| Hierarchy and layout | Few | Reading order against importance; the fold at each geometry; empty or stretched space; responsive behaviour with nothing hidden. |
| Readability | WCAG | Sizes against a 10 px floor for anything a reader must read; computed contrast; colour meaning consistent and colour-vision-safe; overflow. |
| Motion and live data | Nielsen | What redraws, how often, whether it can be read; nothing blinks without meaning; what every readout does when the cursor pauses, scrubs, or goes live. |
| Interaction and state | Nielsen | Each control says what it will do and why it is disabled; every lifecycle state is visibly distinct with its remedy; the keyboard works. |
| Chart integrity | Tufte | Ranges, floors, pads and log scales stated; series told apart by more than hue; the thing the lede points at is visible at the scale drawn. |
| Prior-art faithfulness | Oak Lab | Terms used as the sources use them; every algorithm surface pinned; the mission quoted, not paraphrased; a hand-authored departure never presented as learned. |
| Copy | editor | Plain English first, jargon defined at first use, no marketing, names consistent with the spec, no typographic errors. |


Report a concrete violation with its location, user impact and relevant spec
clause. Label preferences as design judgment. Fix authorized defects, recheck the
affected state and run the viewer/structural gates required by `AGENTS.md`.
No finding IDs, confidence scores, charter, coverage attestation or full report
are required. A useful screenshot and a short explanation are enough.

Preserve observer-only lifecycle control and the spec's timer inventory. Do not
hide data to fit a layout, imply unsupported learning/performance claims, invent
citations or add a scenario/visual-regression test harness. Larger product choices
belong to the owner; style preferences are not blocking defects.
