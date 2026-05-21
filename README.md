# ERD46

A lean formalization of [Erdős Problem 90](https://www.erdosproblems.com/90) *Planar Point Sets with Many Unit Distances* from OpenAI.

The original blog post can be found [here](https://openai.com/index/model-disproves-discrete-geometry-conjecture/)

A lean template can be found [here](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/90.lean)

## HUMAN VERIFICATION

as of commit `101a3ecc08d74757d0ac246664a8d72c80f8756b`

- [x] `Erd46/Defs.lean`
- [ ] `Erd46/Axioms.lean`
- [x] main theorem `erdos_unit_distance_false` in `Erd46/Main.lean`

## INSTRUCTION FOR AI

- this file is strictly for human: DO NOT EDIT, DO NOT COMMIT

- the main theorem must be put in `Erd46/Main.lean`

- all necessary definitions for the main theorem must be put in `Erd46/Defs.lean`

- all proven facts that put as axioms must be put in `Erd46/Axioms.lean`

- you can find some useful resources in `assets`

- your model name is `DeepSeek-V4-Pro with Claude Code`, please end your commit message with 

```
Co-Authored-By: [model name]
```