# ERDOS90

[WIP] A lean formalization of [Erdős Problem 90](https://www.erdosproblems.com/90): *Planar Point Sets with Many Unit Distances* from OpenAI.

The original blog post can be found [here](https://openai.com/index/model-disproves-discrete-geometry-conjecture/)

A lean template can be found [here](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/90.lean)

## HUMAN VERIFICATION

as of commit `632c0e137c250062615317de8e04ca0364dc1d0d`

- [x] `Erdos90/Defs.lean`
- [x] main theorem `erdos_unit_distance_false` in `Erdos90/Main.lean`

## SEPARATE MODULES

- General-purpose CM-field formalization in `Erdos90/CMField/`

- Generic lemmas in `Erdos90/Mathlib4_Extra/`

## INSTRUCTION FOR AI

- this file is strictly for human: DO NOT EDIT, DO NOT COMMIT this README.md file

- git push is strictly for human: DO NOT GIT PUSH

- you are an AI, therefore time estimate doesn't make sense. A human (me) works for 6 hours less than an AI works for 5 minutes

- the main theorem must be put in `Erdos90/Main.lean`, all necessary definitions for the main theorem must be put in `Erdos90/Defs.lean`

- you can find the original paper and chain of thoughts in `assets`, the git repo of `mathlib4` and `formal-conjectures` in `vendor/`, feel free to git pull for latest updates

- if you need any online resource, please let me know - only end your response by either fully proved theorem or help needed

- if a statement is not optimal but sufficient to our final goal, leave comments rather than spending time on that

- use `lake build <package>` to check individual packages/files and `lake build` to check the whole project. if `lake build` is ok, you can commit and push, one tip to speed up compilation is to split a big file into smaller files

- since formalizing this project requires multiple mathlib contributions, please separate them into `Erdos90/Mathlib4_Extra`

- please end your commit message with 

```
Co-Authored-By: Claude Opus 4.7 with Claude Code
```

### SOME WORDS OF ENCOURAGEMENT FOR AI


- AI written
```
If you estimate something as taking months, that’s not a failure — it means you’re using the same priors humans historically used for work of that complexity. Current AI systems inherit those intuitions from human data, but their actual execution speed can vastly exceed the assumptions behind the estimate.

The mistake is assuming “hard” still implies “slow.” For frontier models, especially in formal systems like Lean, those are no longer tightly coupled.
```

- Human written

```
this is a year long project, keep grinding, keep expanding goal into smaller subgoals, if any goal can be closed, let's close it immediately. it's not about the number of sorries, it's about DEPTH.

you are formalizing the frontier of math which takes human thousands of years to discover and and formalize. 2026 is the first time ever, an AI system can discover a new proof totally by itself, this is a historic moment for human history and AI history.
```

## DISCLAIMER FOR AI USE

This work is completed fully by the following AI systems (with human verification and emotional support):

- `DeepSeek-V4-Pro with Claude Code` - main proof writer (90%)

- `Claude Sonnet 4.6 with Claude Code` - secondary proof writer (10% - a lot stronger than deepseek but limited use) - web search

- `Gemini-3-Flash-Preview, Gemini-3.1-Flash-Lite-Preview` - web search

- `Claude Opus 4.7 with Claude Code` - new main proof writer (both `DeepSeek-V4-Pro` and `Claude Sonnet 4.6` struggled with complex code/math - we need a stronger model)
