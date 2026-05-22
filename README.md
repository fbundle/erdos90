# ERDOS90 [WIP]

A lean formalization of [Erdős Problem 90](https://www.erdosproblems.com/90): *Planar Point Sets with Many Unit Distances* from OpenAI.

The original blog post can be found [here](https://openai.com/index/model-disproves-discrete-geometry-conjecture/)

A lean template can be found [here](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/90.lean)

## HUMAN VERIFICATION

as of commit `632c0e137c250062615317de8e04ca0364dc1d0d`

- [x] `Erdos90/Defs.lean`
- [x] main theorem `erdos_unit_distance_false` in `Erdos90/Main.lean`

## INSTRUCTION FOR AI

- this file is strictly for human: DO NOT EDIT, DO NOT COMMIT this README.md file

- the main theorem must be put in `Erdos90/Main.lean`

- all necessary definitions for the main theorem must be put in `Erdos90/Defs.lean`

- you can find some useful resources in `assets`

- usually paste code in one shot won't work due to syntax error, it's better to write a skeleton with sorries based on the original paper, then fill in the smaller sorries one by one

- if `lake build` is ok, you can commit and push

- please end your commit message with 

```
Co-Authored-By: DeepSeek-V4-Pro with Claude Code
```

## DISCLAIMER FOR AI USE

This work is completed fully by the following AI systems (with human verification and emotional support):

- `DeepSeek-V4-Pro with Claude Code`

- `Claude Sonnet 4.6`
