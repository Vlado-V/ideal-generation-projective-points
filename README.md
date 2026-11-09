# Ideal generation for general reduced projective points

The paper and Lean formalization of Theorem 1.1 by Vlado Vojdanovski.

For an algebraically closed field of characteristic zero, general reduced
points in projective space have maximal-rank multiplication from their
initial homogeneous ideal piece by linear forms. The proof gives the exact
numbers of minimal generators in the initial degree and the next degree,
and generation in those two degrees.

- [Paper](Ideal_generation_for_general_reduced_projective_points.pdf)
- [Final theorem](IdealGeneration/TheoremOneOne.lean)
- [Formal statement](IdealGeneration/TheoremOneOneStatement.lean)
- [Detailed development guide](README.txt)
- [Provenance](PROVENANCE.md)
- [Verification log](verification.log)

## Formal statement

The main declaration is `IdealGeneration.theorem_one_one`. It covers every
projective dimension at least one, every initial degree at least two, and
every point count in the initial-degree interval. The open set is a
nonempty principal open in the standard affine chart of the ordered
configuration space. The point family takes values in Mathlib's
`Projectivization`, and its homogeneous ideal is radical.

The multiplication map is the actual map `I_D ⊗ S_1 → I_(D+1)`.
The minimal generating family has the predicted cardinalities and every
generator is indispensable. The degree bound is expressed in the
homogeneous coordinate ring by generation in degrees `D` and `D+1`.

`Challenge.lean` gives the independent Mathlib-only statement.
`Solution.lean` proves that statement from this development.
`comparator.json` selects `IdealGenerationPaper.main_result`.

## Build and verification

The project pins Lean `v4.35.0-rc3` and Mathlib commit
`8accc04827c389e678c3ef83e623b402e7480394`.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
```

`Audit.lean` checks the local declaration closure and rejects axioms other
than `propext`, `Classical.choice`, and `Quot.sound`. The finite matrices
are certified by exact kernel-checked arithmetic.

The Palomar full preflight workflow is manually dispatchable and pins
its verifier revision. The same workflow is required before registry intake.
