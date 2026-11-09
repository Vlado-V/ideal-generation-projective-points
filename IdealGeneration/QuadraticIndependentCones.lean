module

public import IdealGeneration.QuadraticFlag
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Syzygies of the quadrics for independent cone points

After the cone points have been moved to coordinate points, write their
normal forms as `s = ∑ aᵢ Xᵢ` and `t = ∑ bᵢ Xᵢ`. The residual quadrics are
`wᵢ = Xᵢ (bᵢ s - aᵢ t)`. Pairwise distinct normal directions imply that
every linear syzygy between the `wᵢ` comes from their single constant
relation `∑ wᵢ = 0`.
-/

noncomputable section
namespace IdealGeneration.QuadraticIndependentCones
open MvPolynomial
open QuadraticFlag

variable {K I : Type*} [Field K] [Fintype I]

/-- Residual quadrics at coordinate cone points. -/
def residualQuadric (a b : I → K) (i : I) : MvPolynomial I K :=
  X i * (C (b i) * linearPolynomial a - C (a i) * linearPolynomial b)

/-- The redundant generators have their expected constant relation. -/
theorem sum_residualQuadric (a b : I → K) : ∑ i, residualQuadric a b i = 0 := by
  simp_rw [residualQuadric, mul_sub, ← mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  simp_rw [mul_comm (X _) (C _)]
  change linearPolynomial b * linearPolynomial a -
    linearPolynomial a * linearPolynomial b = 0
  ring

/-- The polynomial expression represented by a matrix of linear coefficients. -/
def syzygyExpression (a b : I → K) (L : I → I → K) : MvPolynomial I K :=
  ∑ i, linearPolynomial (L i) * residualQuadric a b i

/-- Retain only two coordinates, putting the first at one and the second at `X`. -/
def lineSubstitution [DecidableEq I] (i j k : I) : Polynomial K :=
  if k = i then 1 else if k = j then Polynomial.X else 0

/-- Restriction to a coordinate affine line. -/
def lineRestriction [DecidableEq I] (i j : I) : MvPolynomial I K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C (lineSubstitution i j)

/-- Restricting a linear form retains precisely its two indicated coefficients. -/
theorem lineRestriction_linearPolynomial [DecidableEq I]
    (i j : I) (hij : i ≠ j) (u : I → K) :
    lineRestriction i j (linearPolynomial u) =
      Polynomial.C (u i) + Polynomial.C (u j) * Polynomial.X := by
  simp [lineRestriction, linearPolynomial, lineSubstitution, mul_ite]
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    (by intro k _ hk; simp [hk.1, hk.2])]
  simp [Ne.symm hij]

omit [Fintype I] in
@[simp] theorem lineRestriction_C [DecidableEq I] (i j : I) (c : K) :
    lineRestriction i j (C c) = Polynomial.C c := by
  simp [lineRestriction]

omit [Fintype I] in
@[simp] theorem lineRestriction_X [DecidableEq I] (i j k : I) :
    lineRestriction (K := K) i j (X k) = lineSubstitution i j k := by
  simp [lineRestriction]

/-- A two-coordinate restriction leaves only the two corresponding residual
quadrics, with opposite coefficients. -/
theorem lineRestriction_residualQuadric [DecidableEq I]
    (a b : I → K) (i j k : I) (hij : i ≠ j) :
    lineRestriction i j (residualQuadric a b k) =
      if k = i then Polynomial.C (b i * a j - a i * b j) * Polynomial.X
      else if k = j then -(Polynomial.C (b i * a j - a i * b j) * Polynomial.X)
      else 0 := by
  simp only [residualQuadric, map_mul, map_sub, lineRestriction_C,
    lineRestriction_X, lineRestriction_linearPolynomial i j hij]
  by_cases hki : k = i
  · subst k
    simp only [lineSubstitution, ↓reduceIte]
    ring
  · by_cases hkj : k = j
    · subst k
      simp only [lineSubstitution, hki, ↓reduceIte]
      ring
    · simp [lineSubstitution, hki, hkj]

/-- The restriction of a linear syzygy factors by the nonzero direction
minor and the coordinate parameter. -/
theorem lineRestriction_syzygyExpression [DecidableEq I]
    (a b : I → K) (L : I → I → K) (i j : I) (hij : i ≠ j) :
    lineRestriction i j (syzygyExpression a b L) =
      (lineRestriction i j (linearPolynomial (L i)) -
        lineRestriction i j (linearPolynomial (L j))) *
        (Polynomial.C (b i * a j - a i * b j) * Polynomial.X) := by
  simp only [syzygyExpression, map_sum, map_mul,
    lineRestriction_residualQuadric a b i j _ hij]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    (by intro k _ hk; simp [hk.1, hk.2])]
  simp [Ne.symm hij, sub_mul]
  ring

/-- The coefficient of a chosen coordinate is equal in the two rows of
any linear syzygy whose normal directions are independent. -/
theorem syzygy_diagonal_coeff_eq (a b : I → K) (L : I → I → K)
    (hL : syzygyExpression a b L = 0) (i j : I)
    (hdet : b i * a j - a i * b j ≠ 0) : L i i = L j i := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    simp [mul_comm] at hdet
  have hr := congrArg (lineRestriction (K := K) i j) hL
  rw [lineRestriction_syzygyExpression a b L i j hij, map_zero] at hr
  have hfactor : Polynomial.C (b i * a j - a i * b j) * Polynomial.X ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hdet) Polynomial.X_ne_zero
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hfactor)
  have hc := congrArg Polynomial.constantCoeff heq
  simpa [lineRestriction_linearPolynomial i j hij] using hc

/-- Every linear syzygy has the same coefficient in each row of every column. -/
theorem syzygy_coefficients_row_constant (a b : I → K) (L : I → I → K)
    (hdir : ∀ i j, i ≠ j → b i * a j - a i * b j ≠ 0)
    (hL : syzygyExpression a b L = 0) :
    ∀ i j k, L i k = L j k := by
  intro i j k
  have column (r : I) : L k k = L r k := by
    by_cases hkr : k = r
    · subst r
      rfl
    · exact syzygy_diagonal_coeff_eq a b L hL k r (hdir k r hkr)
  exact (column i).symm.trans (column j)

/-- Conversely, a common linear coefficient multiplies the redundant
constant relation of the residual quadrics. -/
theorem syzygyExpression_eq_zero_of_row_constant (a b : I → K) (L : I → I → K)
    (hrow : ∀ i j k, L i k = L j k) : syzygyExpression a b L = 0 := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · let := hI
    simp [syzygyExpression]
  · let := hI
    let base : I := Classical.arbitrary I
    have heq (i : I) : linearPolynomial (L i) = linearPolynomial (L base) := by
      congr 1
      funext k
      exact hrow i base k
    simp only [syzygyExpression, heq, ← Finset.mul_sum, sum_residualQuadric, mul_zero]

/-- The complete linear-syzygy classification, uniformly in the number of
independent cone points. -/
theorem syzygyExpression_eq_zero_iff (a b : I → K) (L : I → I → K)
    (hdir : ∀ i j, i ≠ j → b i * a j - a i * b j ≠ 0) :
    syzygyExpression a b L = 0 ↔ ∀ i j k, L i k = L j k :=
  ⟨syzygy_coefficients_row_constant a b L hdir,
    syzygyExpression_eq_zero_of_row_constant a b L⟩

/-- Removing one redundant generator makes multiplication injective. -/
theorem normalized_syzygy_eq_zero (a b : I → K) (L : I → I → K) (base : I)
    (hdir : ∀ i j, i ≠ j → b i * a j - a i * b j ≠ 0)
    (hbase : L base = 0) (hL : syzygyExpression a b L = 0) : L = 0 := by
  funext i k
  have h := syzygy_coefficients_row_constant a b L hdir hL i base k
  simpa [hbase] using h

/-- The multiplication map from all coefficient rows to cubic polynomials. -/
def coneMultiplication (a b : I → K) : (I → I → K) →ₗ[K] MvPolynomial I K where
  toFun := syzygyExpression a b
  map_add' L M := by
    simp [syzygyExpression, linearPolynomial, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
  map_smul' r L := by
    have hlin (i : I) : linearPolynomial ((r • L) i) = r • linearPolynomial (L i) := by
      simp only [linearPolynomial, Pi.smul_apply, smul_eq_mul, map_mul,
        Algebra.smul_def, MvPolynomial.algebraMap_eq, Finset.mul_sum, mul_assoc]
    simp only [syzygyExpression, hlin, Finset.smul_sum, smul_mul_assoc,
      RingHom.id_apply]

/-- Normalize a syzygy by making the coefficient of one redundant generator zero. -/
def normalizedCoefficients (base : I) : Submodule K (I → I → K) :=
  (LinearMap.proj (R := K) (φ := fun _ : I => I → K) base).ker

/-- Multiplication with one redundant generator removed. -/
def normalizedMultiplication (a b : I → K) (base : I) :
    normalizedCoefficients (K := K) base →ₗ[K] MvPolynomial I K :=
  (coneMultiplication a b).comp (normalizedCoefficients base).subtype

/-- The normalized multiplication map is injective for every finite family
of pairwise distinct normal directions. -/
theorem normalizedMultiplication_injective (a b : I → K) (base : I)
    (hdir : ∀ i j, i ≠ j → b i * a j - a i * b j ≠ 0) :
    Function.Injective (normalizedMultiplication a b base) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro L hL
  apply Subtype.ext
  exact normalized_syzygy_eq_zero a b L.val base hdir L.property hL

/-- Removing one coefficient row leaves exactly `N (N-1)` parameters. -/
theorem finrank_normalizedCoefficients (base : I) :
    Module.finrank K (normalizedCoefficients (K := K) base) =
      Fintype.card I * (Fintype.card I - 1) := by
  let p : (I → I → K) →ₗ[K] (I → K) := LinearMap.proj base
  have hsurj : Function.Surjective p := by
    intro v
    exact ⟨fun _ => v, rfl⟩
  have hdim := p.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at hdim
  simp only [finrank_top, Module.finrank_pi, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] at hdim
  change Module.finrank K p.ker = _
  rw [Nat.mul_sub_left_distrib, mul_one]
  omega

/-- The cubic image has the dimension asserted in the independent-cone calculation. -/
theorem finrank_normalizedMultiplication_range (a b : I → K) (base : I)
    (hdir : ∀ i j, i ≠ j → b i * a j - a i * b j ≠ 0) :
    Module.finrank K (normalizedMultiplication a b base).range =
      Fintype.card I * (Fintype.card I - 1) := by
  rw [LinearMap.finrank_range_of_inj (normalizedMultiplication_injective a b base hdir),
    finrank_normalizedCoefficients]

/-- Normalizing the coefficient row does not change the cubic image. -/
theorem normalizedMultiplication_range (a b : I → K) (base : I) :
    (normalizedMultiplication a b base).range = (coneMultiplication a b).range := by
  ext f
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L.val, rfl⟩
  · rintro ⟨L, rfl⟩
    let common : I → I → K := fun _ => L base
    have hcommon : coneMultiplication a b common = 0 :=
      syzygyExpression_eq_zero_of_row_constant a b common (by intros; rfl)
    let reduced : normalizedCoefficients (K := K) base :=
      ⟨L - common, by change L base - L base = 0; exact sub_self _⟩
    refine ⟨reduced, ?_⟩
    change coneMultiplication a b (L - common) = coneMultiplication a b L
    rw [map_sub, hcommon, sub_zero]

/-- All cubic products of the residual quadrics have dimension `N (N-1)`. -/
theorem finrank_coneMultiplication_range (a b : I → K) (base : I)
    (hdir : ∀ i j, i ≠ j → b i * a j - a i * b j ≠ 0) :
    Module.finrank K (coneMultiplication a b).range =
      Fintype.card I * (Fintype.card I - 1) := by
  rw [← normalizedMultiplication_range a b base]
  exact finrank_normalizedMultiplication_range a b base hdir

/-- A constant relation between the residual quadrics also has equal
coefficients. It follows by multiplying the relation by one coordinate. -/
theorem quadric_relation_coefficients_constant (a b c : I → K)
    (hdir : ∀ i j, i ≠ j → b i * a j - a i * b j ≠ 0)
    (hc : ∑ i, C (c i) * residualQuadric a b i = 0) :
    ∀ i j, c i = c j := by
  classical
  intro i j
  let L : I → I → K := fun k r => if r = i then c k else 0
  have hlin (k : I) : linearPolynomial (L k) = C (c k) * X i := by
    simp [linearPolynomial, L, apply_ite, ite_mul]
  have hL : syzygyExpression a b L = 0 := by
    calc
      syzygyExpression a b L = ∑ k, (C (c k) * X i) * residualQuadric a b k := by
        simp only [syzygyExpression, hlin]
      _ = X i * ∑ k, C (c k) * residualQuadric a b k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by rw [hc, mul_zero]
  simpa [L] using syzygy_coefficients_row_constant a b L hdir hL i j i

/-- After deleting one redundant generator, a constant relation is trivial. -/
theorem normalized_quadric_relation (a b c : I → K) (base : I)
    (hdir : ∀ i j, i ≠ j → b i * a j - a i * b j ≠ 0)
    (hbase : c base = 0) (hc : ∑ i, C (c i) * residualQuadric a b i = 0) : c = 0 := by
  funext i
  exact (quadric_relation_coefficients_constant a b c hdir hc i base).trans hbase

/-- The quadrics indexed away from one base point are linearly independent. -/
theorem residualQuadrics_without_base_linearIndependent (a b : I → K) (base : I)
    (hdir : ∀ i j, i ≠ j → b i * a j - a i * b j ≠ 0) :
    LinearIndependent K (fun i : {i : I // i ≠ base} => residualQuadric a b i.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let extended : I → K := fun j => if h : j = base then 0 else c ⟨j, h⟩
  have hbase : extended base = 0 := by simp [extended]
  have hext : ∑ j, C (extended j) * residualQuadric a b j = 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ base)]
    rw [Finset.sum_subtype (p := fun j : I => j ≠ base)
      (Finset.univ.erase base) (by intro j; simp)]
    have hterm (x : {j : I // j ≠ base}) : extended x.val = c x := by
      simp [extended, x.property]
    simpa only [hterm, hbase, map_zero, zero_mul, add_zero,
      Algebra.smul_def, MvPolynomial.algebraMap_eq] using hc
  have hz := normalized_quadric_relation a b extended base hdir hbase hext
  have hi := congrFun hz i.val
  simpa [extended, i.property] using hi

/-- The explicit directions `(1,i)` are pairwise independent in every
characteristic-zero field, for arbitrarily many indices. -/
theorem natural_directions_independent [CharZero K] (N : ℕ) (i j : Fin N)
    (hij : i ≠ j) : (i.val : K) * 1 - 1 * (j.val : K) ≠ 0 := by
  have hcast : (i.val : K) ≠ (j.val : K) := by
    intro h
    exact hij (Fin.ext (Nat.cast_injective h))
  simpa only [mul_one, one_mul] using sub_ne_zero.mpr hcast

/-- A concrete infinite family realizing the independent-cone multiplication rank. -/
theorem natural_directions_cubic_rank [CharZero K] (N : ℕ) (base : Fin N) :
    Module.finrank K (coneMultiplication (fun _ : Fin N => (1 : K))
      (fun i : Fin N => (i.val : K))).range = N * (N - 1) := by
  simpa using finrank_coneMultiplication_range (fun _ : Fin N => (1 : K))
    (fun i : Fin N => (i.val : K)) base (natural_directions_independent N)

end IdealGeneration.QuadraticIndependentCones
