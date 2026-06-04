[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# Challenge 3

The formal proofs provided in this work were developed and verified using **Lean 4.28.0**. Compatibility with earlier or later versions is not guaranteed due to the evolving nature of the Lean 4 compiler and its core libraries.

## Repository structure

This repository collects several formalization runs, each in its own subdirectory
(`prop1`, `prop2`):

- Inputs for each run live under [`input/<run>/`](input/).
- Lean outputs for each run live under [`Challenge_3/<run>/`](Bijection/).

## Input files

For each part, [`input/<part>/`](input/) contains:

- `problem.md`: the task description, including the Lean scaffold (definitions and lemma
  statements) the formalization must follow.
- `challenge3_Part*.tex`: the LaTeX statement and proof that the formalization follows.


## Output files
- `problem.lean`: translation of the problem statement into Lean (definitions, with the
  target statements left as `sorry`).
- `solution.lean`: the complete formal solution, with no `sorry`.


## License

This repository uses the MIT License. See [LICENSE](LICENSE) for details.

## Repository maintainers

- [Evan Chen](https://github.com/vEnhance)
- [Kenny Lau](https://github.com/kckennylau)
- [Ken Ono](https://github.com/kenono691)
- [Jujian Zhang](https://github.com/jjaassoonn)
