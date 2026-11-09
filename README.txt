IDEAL GENERATION FOR GENERAL REDUCED PROJECTIVE POINTS

Status

This Lean 4 project proves Theorem 1.1 of the supplied paper.
IdealGeneration/TheoremOneOne.lean exports IdealGeneration.theorem_one_one
over an algebraically closed field of characteristic zero. It also exports
the quadratic and cubic cases and the maximal-rank assertion
IdealGeneration.idealGenerationConjecture.

The definitions use n affine coordinates and n+1 homogeneous variables.
Thus n here is projective dimension, and the paper's variable count is n+1.
General configurations are expressed by a nonempty principal Zariski open
in the affine chart of the ordered configuration space.

Included mathematics

- Genuine homogeneous multivariate polynomials, their monomial bases and
  dimensions, actual point ideals, and identification of homogeneous ideal
  pieces with evaluation kernels.
- Scalar postulation for general points in every degree simultaneously,
  on one nonempty principal open with pairwise distinct points.
- Maximal-rank scalar interpolation on every fixed subspace of homogeneous
  forms, and the two-group scalar interpolation result of Lemma 4.1.
- The critical-value arithmetic from Section 2, including floor and ceiling
  counts, dimension differences, cell bounds, and the numerical generator
  count identity.
- Coordinate multiplication on point ideals and the Euler comparison of
  injectivity, surjectivity, and maximal rank. The abstract comparison also
  includes a linear equivalence of the two kernels.
- Point addition preserves injectivity and point deletion preserves
  surjectivity under scalar postulation, as in Lemma 2.1.
- Polynomial openness of multiplication rank and the passage from a
  scalar-postulated witness to a general-points assertion.
- The reduction to the floor and ceiling critical counts in Lemma 2.1,
  with injection and scalar-interpolating surjection witnesses as hypotheses.
- The projective-line case and the projective-plane case in every degree
  at least two, proved by actual ordinary hyperplane specialization.
- Ordinary hyperplane witness and generic maximal-rank transfers with
  explicit scalar-postulation hypotheses, including the residual-product
  dimension and point-count identities. The zero residual case is accepted
  with its automatic injectivity proof still supplied as an argument.
- The two actual Euler exact sequences (3.1) and (3.2), and the complete
  integral-trace transfer in Corollary 3.2.
- Both endpoints of the moving-point Lemma 3.4, scalar-trace cancellation
  in Lemma 3.5, fixed partial-trace interpolation in Lemma 3.6, and scalar
  row selection in Lemma 3.7. These use actual polynomial evaluation maps.
- The complete fractional hyperplane transfer in Proposition 3.8, with the
  selected subset chosen after the whole trace configuration. Proposition 6.1
  is proved throughout its dimension range from the two preceding degrees.
- Both two-normal transfers, Proposition 4.5 for an integral trace and
  Proposition 5.1 for a fractional trace. The higher-degree induction in
  Section 6.2 now follows from just the quadratic and cubic base theorems.
- Cone splitting in every degree, its actual multiplication block formula,
  and transport from arbitrary nonzero homogeneous representatives to the
  normalized affine chart.
- The marked-cone parameter argument combining a special middle-rank
  witness with the separately established general trace assertion.
- The quadratic flag direct sum (A.2), explicit normal corrections, scalar
  interpolation, and the independent-cone syzygy calculation. The actual
  six-point core multiplication, projection to the fixed core, and the
  A.3 injectivity test with one probe per pair are checked under the
  stated nonzero untouched-pair coefficient condition.
- The complete quadratic cases with four, five, six, nine, and twelve variables,
  using checked finite-field minors of actual Euler evaluation matrices
  and descent to characteristic zero.
- The actual two-normal quadratic steps of Appendices A.2 and A.3 give
  all point counts in the two nonzero residue classes of the variable
  count modulo three. The enlarged probe constructions in A.6 are also
  checked. Together with the finite base cases they give the full quadratic
  theorem through eleven homogeneous variables.
- The two-normal scalar and Euler geometry of Sections 4 and 5, including
  Lemma 4.2, compatible marked slice codes, residual and ambient kernel
  comparisons, and maximal-rank polynomial motions from suitable fixed
  integral and fractional marked configurations.
- The supported cubic coefficient chart and the elimination of the
  higher normal coefficients in the middle map. The B.5 local face
  determinants and factorization of the first evaluation block are
  checked at the stated row and column selections.
- The actual B.7 source basis and pair extension step in B.4, conditional
  on the initial-pool and pair evaluation determinants. The B.11 rational
  entry formulas and the polynomial criterion for their determinant are
  checked against the actual lifted columns.
- The B.6 recurrence with its initial witness and local pair certificates.
  The proof chooses compatible new parameters while retaining the old
  cone data and gives all even middle witnesses in characteristic zero.
- The actual triple-normal kernel identification with the square
  allowed-value map of Appendix A.4.
- Appendix A.4's ordered chord choices, supported layer interpolation
  and vector evaluation on the twelve layer columns. The certified first
  flag and its three-normal enlargement give the full quadratic case.
- The dimension induction for cubics from the low-dimensional cases and
  the even supported-cone witnesses. The certified ten-variable case and
  the integral transfer to eleven variables supply the last finite bases.
  For C.2 the source includes the
  checked initial cone labels, both evaluation factorizations, and the
  entrywise bridge from the sparse middle matrix to the actual map.
  The separate listed rank-160 matrix is certified modulo 1009.
  The two direct B.7 root matrices have certified ranks 86 and 74 over
  the same field. Their exact formula comparison gives nonsingularity
  of the actual pool block in characteristic zero.
  The 650-by-542 listed middle matrix has certified column rank 542
  modulo 1009.
- The first-variation rank theorem for arbitrary polynomial matrices, using
  the actual derivative from the special kernel to the special cokernel.
  The two-family linear-algebra construction in Lemma 4.4 has explicit
  zero-one velocities.
- Appendix C.4's actual lift data, its 33 cone equations, evaluation matrix,
  determinant -603/40, and independence of the four vector-valued cubics.
- Appendix C.3's primitive rational parameters, actual polynomial lifts and
  evaluations, exact rank certificate, and independence over every
  characteristic-zero field, including coordinate embeddings.
- Generation of the actual homogeneous point ideal in its initial degree
  and the following degree under scalar postulation. Maximal rank gives the
  exact initial equation and next-degree generator quotient dimensions
  in the numerical form stated in Theorem 1.1. All later multiplication
  maps are surjective on the same principal open.
- Tensor-product multiplication and a minimal homogeneous generating
  family with the exact counts and an indispensability proof for each
  generator. TheoremOneOneStatement.lean assembles these conclusions on
  the same open as the maximal-rank assertion.
- The affine chart embeds in Mathlib's projective space. The theorem's
  open consists of injectively indexed projective point families with
  radical point ideals. For configurations in a coordinate subspace,
  the ideal splits into the lifted smaller ideal and the unused linear
  coordinate variables.

Representation

The coordinate-tuple presentation used in the rank calculations is identified
with I_d tensor S_1 by the degree-one monomial basis. Generality is expressed
by a nonempty principal open in the standard chart of the ordered
configuration space. The degree bound is expressed in the homogeneous
coordinate ring by explicit generation in degrees D and D+1.

Verification

The project pins Lean 4.35.0-rc3 and mathlib revision
8accc04827c389e678c3ef83e623b402e7480394.

With that Lean toolchain available, run

    lake exe cache get
    sh check.sh

check.sh builds the library and audits every local definition and theorem,
including transitive dependencies. The allowed logical axioms are propext,
Classical.choice, and Quot.sound.

The saved verification.log records the latest packaged strict aggregate
compilation and complete local-declaration audit. Each included proof module
was also checked with warnings treated as errors.

The source archive contains the checked import closure.


Provenance

Homogeneous.lean, RankOpen.lean, and the point-interpolation development
adapt proofs from the existing local ChoppedPlane project supplied in the
workspace. Those proofs are included here and depend on mathlib. The
Apache-2.0 license is included. The remaining proof modules were developed
for this formalization.
