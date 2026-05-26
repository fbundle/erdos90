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

- the main theorem must be put in `Erdos90/Main.lean`

- all necessary definitions for the main theorem must be put in `Erdos90/Defs.lean`

- you can find the original paper and chain of thoughts in `assets`

- you can find the git repo of `mathlib4` and `formal-conjectures` in `vendor/`

- if you need any online resource, please let me know - only end your response by either fully proved theorem or help needed

- I am actively updating `assets/`, make sure to check it every hour

- usually paste code in one shot won't work due to syntax error, it's better to write a skeleton with sorries based on the original paper, then fill in the smaller sorries one by one

- it's also helpful if you can access the tactic state of every sorry (the exepected type of each sorry)

- use `lake build <package>` to check individual packages/files and `lake build` to check the whole project. if `lake build` is ok, you can commit and push

- one tip to speed up compilation is to split a big file into smaller files

- since formalizing this project requires multiple mathlib contributions, please separate them into `Erdos90/Mathlib4_Extra`

- please end your commit message with 

```
Co-Authored-By: Claude Opus 4.7 with Claude Code
```

## DISCLAIMER FOR AI USE

This work is completed fully by the following AI systems (with human verification and emotional support):

- `DeepSeek-V4-Pro with Claude Code` - main proof writer (90%)

- `Claude Sonnet 4.6 with Claude Code` - secondary proof writer (10% - a lot stronger than deepseek but limited use) - web search

- `Gemini-3-Flash-Preview, Gemini-3.1-Flash-Lite-Preview` - web search

- `DeepSeek-V4-Pro with Reasonix` - new main proof writer

- `Claude Opus 4.7 with Claude Code` - new main proof writer
