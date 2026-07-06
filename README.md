# Lean Schroeder-Bernstein Theorem

This repository contains a Lean 4 formalization of an alternative proof of the
Schroeder-Bernstein theorem, developed for a July 2025 presentation with Eric.

The Schroeder-Bernstein theorem states that if there is an injection
`f : alpha -> beta` and an injection `g : beta -> alpha`, then there exists a
bijection between `alpha` and `beta`.

## Main Result

The main theorem is proved in [`alternative_proof.lean`](alternative_proof.lean):

```lean
theorem schroeder_bernstein [Nonempty beta]
    {f : alpha -> beta} {g : beta -> alpha}
    (hf : Injective f) (hg : Injective g) :
    exists h : alpha -> beta, Bijective h
```

The proof follows the standard construction:

1. Build a sequence of subsets `sbAux` of `alpha`.
2. Define `sbSet` as the union of those subsets.
3. Use `f` on `sbSet`.
4. Use the inverse of `g` on the complement of `sbSet`.
5. Glue the two bijections together across disjoint partitions.

## Repository Structure

- [`alternative_proof.lean`](alternative_proof.lean): the Lean 4 proof.
- [`README.md`](README.md): project overview and usage notes.

## Requirements

This proof uses Lean 4 and Mathlib.

The file imports:

```lean
import Mathlib.Tactic
import Mathlib.Data.Set.Function
```

To check the proof, run it inside a Lean 4 project with Mathlib available.

## Notes

The Lean file includes several helper results about `BijOn`, images of unions,
set differences, and gluing bijections over disjoint subsets. Some exploratory
`#check` and `#print` commands are also kept in the file because they document
the process of finding the relevant Mathlib definitions and lemmas.
