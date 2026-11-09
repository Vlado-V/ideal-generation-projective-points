module

public import IdealGeneration.CriticalOpen
public import IdealGeneration.GenericMatrixDescent
public import IdealGeneration.TwoGroupLinearCore

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Integer minors of actual quadratic Euler evaluations give quadratic witnesses. -/

noncomputable section
namespace IdealGeneration.QuadraticLowDimension
open MvPolynomial Module
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n p r : ℕ}

/-- A coefficient-one quadratic monomial. -/
def quadraticForm (K : Type*) [Field K] (i k : Fin (n + 1)) : Forms K (n + 1) 2 :=
  ⟨X i * X k, (isHomogeneous_X (R := K) i).mul (isHomogeneous_X (R := K) k)⟩

@[simp] theorem quadraticForm_val (i k : Fin (n + 1)) :
    (quadraticForm K i k).val = X i * X k := rfl

private theorem formMultiplication_single_val (j : Fin (n + 1))
    (f : Forms K (n + 1) 2) :
    (formMultiplication K (n + 1) 2 (Pi.single j f)).val = X j * f.val := by
  rw [formMultiplication_val, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    simp
  · simp

private def quadraticEulerTuple (K : Type*) [Field K]
    (c : Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) : Fin (n + 1) → Forms K (n + 1) 2 :=
  Pi.single c.2.1 (quadraticForm K c.1 c.2.2) -
    Pi.single c.1 (quadraticForm K c.2.1 c.2.2)

/-- A quadratic Euler column is a coordinate multiple of a Koszul relation. -/
def quadraticEulerColumn (K : Type*) [Field K]
    (c : Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) : EulerRelations K n 2 := by
  refine ⟨quadraticEulerTuple K c, ?_⟩
  apply Subtype.ext
  unfold quadraticEulerTuple
  rw [map_sub]
  simp only [Submodule.coe_sub, Submodule.coe_zero, formMultiplication_single_val,
    quadraticForm_val]
  ring

/-- The integer representative of a point in the standard affine chart. -/
def integerChartRepresentative (a : Fin p × Fin n → ℤ) (i : Fin p) : Fin (n + 1) → ℤ :=
  Fin.snoc (fun j => a (i, j)) 1

/-- Integer affine coordinates viewed in a characteristic-zero field. -/
def integerChartCoordinates (K : Type*) [Field K] (a : Fin p × Fin n → ℤ) :
    PointCoordinates K n p := fun ij => (a ij : K)

@[simp] theorem chartPoint_integerChartCoordinates (a : Fin p × Fin n → ℤ)
    (i : Fin p) (j : Fin (n + 1)) :
    chartPoint K (integerChartCoordinates K a) i j =
      (integerChartRepresentative a i j : K) := by
  refine Fin.lastCases ?_ (fun k => ?_) j <;>
    simp [integerChartCoordinates, integerChartRepresentative]

/-- The integer minor of the Euler evaluation on the selected coordinates
and the selected Koszul columns. -/
def quadraticMinorMatrix (a : Fin p × Fin n → ℤ) (rows : Fin r → Fin p × Fin n)
    (cols : Fin r → Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j =>
    let x := integerChartRepresentative a (rows i).1
    let l := (rows i).2.castSucc
    let c := cols j
    (if l = c.2.1 then x c.1 * x c.2.2 else 0) -
      (if l = c.1 then x c.2.1 * x c.2.2 else 0)

/-- The selected scalar coordinates of the full Euler evaluation target. -/
def minorProjection (K : Type*) [Field K] (rows : Fin r → Fin p × Fin n) :
    (Fin (n + 1) → Fin p → K) →ₗ[K] (Fin r → K) where
  toFun f i := f (rows i).2.castSucc (rows i).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Each column of the integer minor is the indicated actual polynomial evaluation. -/
theorem quadraticMinorMatrix_col (a : Fin p × Fin n → ℤ)
    (rows : Fin r → Fin p × Fin n)
    (cols : Fin r → Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) (j : Fin r) :
    minorProjection K rows
      (eulerEvaluation (integerChartCoordinates K a) 2 (quadraticEulerColumn K (cols j))) =
      (quadraticMinorMatrix a rows cols |>.map (Int.castRingHom K)).col j := by
  funext i
  change eval (chartPoint K (integerChartCoordinates K a) (rows i).1)
    (quadraticEulerTuple K (cols j) (rows i).2.castSucc).val = _
  by_cases hfirst : (rows i).2.castSucc = (cols j).2.1 <;>
    by_cases hsecond : (rows i).2.castSucc = (cols j).1 <;>
    simp [quadraticEulerTuple, quadraticMinorMatrix, Matrix.col, Pi.single_apply,
      hfirst, hsecond, eq_comm]
  all_goals split_ifs <;> simp

/-- A nonsingular minor gives independent actual Euler evaluations. -/
theorem quadraticMinor_rank_lower (a : Fin p × Fin n → ℤ)
    (rows : Fin r → Fin p × Fin n)
    (cols : Fin r → Fin (n + 1) × Fin (n + 1) × Fin (n + 1))
    (hdet : ((quadraticMinorMatrix a rows cols).map (Int.castRingHom K)).det ≠ 0) :
    r ≤ finrank K (eulerEvaluation (integerChartCoordinates K a) 2).range := by
  let f := eulerEvaluation (integerChartCoordinates K a) 2
  let q : Fin r → (Fin (n + 1) → Fin p → K) := fun j => f (quadraticEulerColumn K (cols j))
  have hq : LinearIndependent K q := by
    apply LinearIndependent.of_comp (minorProjection K rows)
    have heq : minorProjection K rows ∘ q =
        ((quadraticMinorMatrix a rows cols).map (Int.castRingHom K)).col := by
      funext j
      exact quadraticMinorMatrix_col a rows cols j
    rw [heq]
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hspan : Submodule.span K (Set.range q) ≤ f.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨quadraticEulerColumn K (cols j), rfl⟩
  have hdim := Submodule.finrank_mono hspan
  rwa [finrank_span_eq_card hq, Fintype.card_fin] at hdim

/-- The actual quadratic Euler source has the expected dimension. -/
theorem quadraticEuler_finrank [CharZero K] (n : ℕ) :
    finrank K (EulerRelations K n 2) = (n + 1) * N (n + 1) 2 - N (n + 1) 3 := by
  have h := TwoGroup.rank_nullity_monoid (formMultiplication K (n + 1) 2)
  rw [LinearMap.range_eq_top.mpr (formMultiplication_surjective (n + 1) 2), finrank_top] at h
  have hsource : finrank K (Fin (n + 1) → Forms K (n + 1) 2) = (n + 1) * N (n + 1) 2 := by
    simp only [Module.finrank_pi_fintype, finrank_forms, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp [N]
  have htarget : finrank K (Forms K (n + 1) 3) = N (n + 1) 3 := finrank_forms K (n + 1) 3
  rw [hsource, htarget] at h
  change finrank K (formMultiplication K (n + 1) 2).ker = _
  omega

/-- Full Euler-fiber evaluation supplies scalar postulation in the same
configuration by taking one tangential component. -/
theorem scalar_surjective_of_euler_fiber_surjective (hn : 1 ≤ n)
    (a : PointCoordinates K n p) (d : ℕ)
    (hs : Function.Surjective (pointEulerSquare a d).leftOnKernel) :
    Function.Surjective (pointEvaluation K a d) := by
  intro w
  let j : Fin n := ⟨0, hn⟩
  let b : Fin n → Fin p → K := Pi.single j w
  let v : Fin (n + 1) → Fin p → K := Fin.snoc b
    (fun i => -∑ l : Fin n, chartPoint K a i l.castSucc * b l i)
  have hv : v ∈ (fiberMultiplication a).ker := by
    change fiberMultiplication a v = 0
    funext i
    change (∑ l, chartPoint K a i l * v l i) = 0
    rw [Fin.sum_univ_castSucc]
    simp [v]
  obtain ⟨f, hf⟩ := hs ⟨v, hv⟩
  refine ⟨f.val j.castSucc, ?_⟩
  have he := congrFun (congrArg Subtype.val hf) j.castSucc
  change pointEvaluation K a d (f.val j.castSucc) = v j.castSucc at he
  simpa [v, b] using he

/-- A minor as large as the Euler source certifies the injective critical side. -/
theorem idealGenerationAt_of_quadratic_minor_injective [CharZero K] (hn : 1 ≤ n)
    (a : Fin p × Fin n → ℤ) (rows : Fin r → Fin p × Fin n)
    (cols : Fin r → Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) (prime : ℕ)
    (hdet : ((quadraticMinorMatrix a rows cols).map (Int.castRingHom (ZMod prime))).det ≠ 0)
    (hsize : (n + 1) * N (n + 1) 2 - N (n + 1) 3 ≤ r) :
    IdealGenerationAt K n 2 p := by
  let z := integerChartCoordinates K a
  let f := eulerEvaluation z 2
  have hr := quadraticMinor_rank_lower (K := K) a rows cols
    (integer_matrix_det_ne_zero_over (quadraticMinorMatrix a rows cols) prime hdet)
  change r ≤ finrank K f.range at hr
  have hnull := TwoGroup.rank_nullity_monoid f
  rw [quadraticEuler_finrank (K := K) n] at hnull
  have hk : finrank K f.ker = 0 := by omega
  let : AddCommGroup (EulerRelations K n 2) := Module.addCommMonoidToAddCommGroup K
  have hi : Function.Injective f := LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
  apply idealGenerationAt_of_injective_witness hn z
  apply (pointMultiplication_injective_iff z 2).mpr
  apply (pointEulerSquare z 2).injective_iff.mpr
  exact (eulerEvaluation_injective_iff z 2).mp hi

/-- A minor as large as the Euler fiber certifies the surjective critical side. -/
theorem idealGenerationAt_of_quadratic_minor_surjective [CharZero K] (hn : 1 ≤ n)
    (a : Fin p × Fin n → ℤ) (rows : Fin r → Fin p × Fin n)
    (cols : Fin r → Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) (prime : ℕ)
    (hdet : ((quadraticMinorMatrix a rows cols).map (Int.castRingHom (ZMod prime))).det ≠ 0)
    (hsize : n * p ≤ r) :
    IdealGenerationAt K n 2 p := by
  let z := integerChartCoordinates K a
  have hr := quadraticMinor_rank_lower (K := K) a rows cols
    (integer_matrix_det_ne_zero_over (quadraticMinorMatrix a rows cols) prime hdet)
  change r ≤ finrank K (eulerEvaluation z 2).range at hr
  have hle := eulerEvaluation_range_le z 2
  have hdim : finrank K (eulerEvaluation z 2).range = finrank K (fiberMultiplication z).ker := by
    have hu := Submodule.finrank_mono hle
    rw [finrank_fiberMultiplication_ker] at hu ⊢
    omega
  have hfull := Submodule.eq_of_le_of_finrank_eq hle hdim
  have hs := (eulerEvaluation_range_eq_iff z 2).mp hfull
  have hscalar := scalar_surjective_of_euler_fiber_surjective hn z 2 hs
  apply idealGenerationAt_of_witness hn z hscalar
  right
  apply (pointMultiplication_surjective_iff z 2).mpr
  exact ((pointEulerSquare z 2).surjective_iff (formMultiplication_surjective (n + 1) 2)
    (componentEvaluation_surjective z hscalar)).mpr hs

end IdealGeneration.QuadraticLowDimension
