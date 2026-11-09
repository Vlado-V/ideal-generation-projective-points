# Provenance

The mathematical source is Vlado Vojdanovski's
*Ideal generation for general reduced projective points*, included as
`Ideal_generation_for_general_reduced_projective_points.pdf`.
The formalization follows Theorem 1.1 and the constructions and reductions
in Sections 2–6 and Appendices A–C.

Vlado Vojdanovski is the author and responsible maintainer. OpenAI Codex
agents assisted with Lean development, exact finite certificates and
internal reviews.

The homogeneous-space, point-ideal and rank-open infrastructure adapts the
author's Apache-2.0 ChoppedPlane development. Homogeneous monomial bases and
dimension arguments derive from the author's Quartic development, and the
homogeneous evaluation scaling argument adapts `OAI.Nagata.W16`. The source
comments retain those credits. `formalization.yaml` links the earlier
developments.

The original completed development was checked with Lean and audited for
its local declaration closure. The publication copy ports the source to
Lean's module system. The documented `backward.privateInPublic` and
`backward.proofsInPublic` compatibility options retain the legacy
definition visibility and proof inference during this port. The publication
audit checks the resulting logical dependencies. The twelve-variable certificate is split at a
declaration boundary into data and proof modules to keep each file below
10,000 lines. Its independent row checks are grouped into six proof modules
to bound compilation memory. Two finite case aggregations use balanced
applications of the existing finite-index lemmas. Its arithmetic leaf
proof bodies are retained. Four helper
lemmas in `CubicInitialStructured.lean` are public so they can occur in the
public structure's proof fields under the module system. The column-permutation
injectivity lemma in `CubicTenShift.lean` is exposed for the same reason.
The base-case coordinate equality in `QuadraticMiddleRank.lean` uses an explicit
pointwise proof in place of the former simplifier call.
The C.3 off-diagonal coefficient comparison uses the existing rational edge
equations and uniqueness of the two-slope solve. This bounds the independent
checker's stack use during verification.
The rational lift algorithm is identified with the coefficient table using
its certified vertex and edge equations. The rational evaluation matrix is
checked one entry at a time with `norm_num` and combined using the finite-index
lemmas.

`SOURCE_MANIFEST.json` records the source files and their SHA-256 digests.
The standalone Challenge states the mathematical claim independently of
the proof development, and the Solution supplies its proof.
