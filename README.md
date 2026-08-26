[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# Challenge 3

The formal proofs provided in this work were developed and verified using **Lean 4.28.0**. Compatibility with earlier or later versions is not guaranteed due to the evolving nature of the Lean 4 compiler and its core libraries.

## Repository structure

This repository collects several formalization runs, each in its own subdirectory
(`lemma-b2`, `lemma-b3`):

- Inputs for each run live under [`input/<run>/`](input/).
- Lean outputs for each run live under [`Challenge_3/<run>/`](Challenge_3/).

## Input files

For each part, [`input/<part>/`](input/) contains:

- `problem.md`: the task description, including the Lean scaffold (definitions and lemma
  statements) the formalization must follow.
- `challenge3_Part*.tex`: the LaTeX statement and proof that the formalization follows.


## Output files
- `problem.lean`: translation of the problem statement into Lean (definitions, with the
  target statements left as `sorry`).
- `solution.lean`: the complete formal solution, with no `sorry`.


## Verifying with Comparator

This repository can be verified against the formal problem statement with the Lean comparator on a Linux machine. First, follow the instructions in [https://github.com/leanprover/comparator](https://github.com/leanprover/comparator) to install comparator. Then, run the following command:

```
lake env comparator comparator-lemma_b2.json
lake env comparator comparator-lemma_b3.json
```

## License

This repository uses the MIT License. See [LICENSE](LICENSE) for details.

## Repository maintainers

- [Evan Chen](https://github.com/vEnhance)
- [Kenny Lau](https://github.com/kckennylau)
- [Ken Ono](https://github.com/kenono691)
- [Jujian Zhang](https://github.com/jjaassoonn)
