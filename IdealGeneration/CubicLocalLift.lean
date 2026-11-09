module

public import IdealGeneration.CubicSupportedC3
public import IdealGeneration.CubicNormalExpansion

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Local coefficient formulas for the mixed and single-edge cubic lifts. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Parameters

open CubicNormalExpansion MvPolynomial

variable {K : Type*} [Field K] {m : ℕ} (P : Parameters K m)

/-- A mixed normal quadratic in one trace slot. -/
def mixedArray (c : Fin m) (Q : Fin 3 → K) : Fin m → Fin 3 → K :=
  fun i => if i = c then Q else 0

/-- The supported lift of a mixed quadratic at one center, with zero single-edge coordinates. -/
def mixedCubic (c : Fin m) (Q : Fin 3 → K) : P.coefficientKernel :=
  P.coefficientLift 0 (mixedArray c Q) 0

/-- Coefficients of the vector-valued linear correction in a mixed lift. -/
def mixedLinear (c : Fin m) (Q : Fin 3 → K) (j : Fin m) : Fin 2 → K :=
  if h : c < j then (P.mixedCubic c Q).val.2.2.2 ⟨(c, j), h⟩
  else if h : j < c then (P.mixedCubic c Q).val.2.2.2 ⟨(j, c), h⟩
  else (P.mixedCubic c Q).val.2.2.1 c

private theorem diagonalLift_zero_at (B : Fin m → Fin 3 → K) (i : Fin m) (h : B i = 0) :
    P.diagonalLift 0 B i = 0 := by
  funext k
  fin_cases k <;> simp [diagonalLift, diagonalRhs, solveTwo, normalCubic, normalQuadratic, h]

private theorem edgeRhs_zero_at (B : Fin m → Fin 3 → K) (e : Edge m) (d : Fin 2)
    (hi : B e.val.1 = 0) (hj : B e.val.2 = 0) :
    P.edgeRhs 0 B e d = 0 := by
  simp [edgeRhs, normalCubic, normalQuadratic, normalLinear, hi, hj,
    P.diagonalLift_zero_at B _ hi, P.diagonalLift_zero_at B _ hj]

private theorem offDiagonalLift_zero_at (B : Fin m → Fin 3 → K) (e : Edge m)
    (hi : B e.val.1 = 0) (hj : B e.val.2 = 0) :
    P.offDiagonalLift 0 B 0 e = 0 := by
  by_cases hs : P.single e = true
  all_goals
    funext k
    fin_cases k <;>
      simp [offDiagonalLift, hs, P.edgeRhs_zero_at B e 0 hi hj, P.edgeRhs_zero_at B e 1 hi hj,
        solveTwo]

/-- The only diagonal coefficient is at the mixed lift's center. -/
theorem mixedCubic_diagonal (c : Fin m) (Q : Fin 3 → K) :
    (P.mixedCubic c Q).val.2.2.1 = starDiagonal c (P.mixedLinear c Q) := by
  funext i k
  by_cases hi : i = c
  · subst i
    simp [starDiagonal, mixedLinear]
  · change P.diagonalLift 0 (mixedArray c Q) i k = _
    rw [P.diagonalLift_zero_at _ i (by simp [mixedArray, hi])]
    simp [starDiagonal, hi]

/-- Only edges incident to the center contribute to the mixed lift. -/
theorem mixedCubic_offDiagonal (c : Fin m) (Q : Fin 3 → K) :
    (P.mixedCubic c Q).val.2.2.2 = starOffDiagonal c (P.mixedLinear c Q) := by
  funext e k
  by_cases h1 : e.val.1 = c
  · have h : c < e.val.2 := h1 ▸ e.property
    simp [starOffDiagonal, h1, mixedLinear, h]
    exact congrArg (fun b : Edge m => (P.mixedCubic c Q).val.2.2.2 b k)
      (Subtype.ext (Prod.ext h1 rfl))
  · by_cases h2 : e.val.2 = c
    · have h : e.val.1 < c := h2 ▸ e.property
      simp [starOffDiagonal, h1, h2, mixedLinear, h, not_lt_of_ge h.le]
      exact congrArg (fun b : Edge m => (P.mixedCubic c Q).val.2.2.2 b k)
        (Subtype.ext (Prod.ext rfl h2))
    · change P.offDiagonalLift 0 (mixedArray c Q) 0 e k = _
      rw [P.offDiagonalLift_zero_at _ e (by simp [mixedArray, h1]) (by simp [mixedArray, h2])]
      simp [starOffDiagonal, h1, h2]

/-- The normal-linear coefficient of the mixed lift factors through its center coordinate. -/
theorem traceA_mixedCubic (c : Fin m) (Q : Fin 3 → K) (k : Fin 2) :
    traceA (P.mixedCubic c Q).val k =
      X c * ∑ j, C (P.mixedLinear c Q j k) * X j := by
  unfold traceA
  rw [P.mixedCubic_diagonal, P.mixedCubic_offDiagonal]
  have hD : (fun i a => (C (starDiagonal c (P.mixedLinear c Q) i a) : Poly K m)) =
      starDiagonal c (fun i a => C (P.mixedLinear c Q i a)) := by
    funext i a
    by_cases hi : i = c <;> simp [starDiagonal, hi]
  have hE : (fun e a => (C (starOffDiagonal c (P.mixedLinear c Q) e a) : Poly K m)) =
      starOffDiagonal c (fun i a => C (P.mixedLinear c Q i a)) := by
    funext e a
    by_cases hi : e.val.1 = c
    · simp [starOffDiagonal, hi]
    · by_cases hj : e.val.2 = c <;> simp [starOffDiagonal, hi, hj]
  simp_rw [map_upperCoefficient]
  rw [hD, hE, traceQuadratic_star]

/-- A unit single-edge coordinate, producing the pure lower lift. -/
def edgeCubic (e : P.SingleEdge) : P.coefficientKernel :=
  P.coefficientLift 0 0 (fun e' => if e' = e then 1 else 0)

/-- The coefficient vector of the graph normal form at a single edge. -/
def edgeLinear (e : P.SingleEdge) : Fin 2 → K := ![P.edgeSlope e.val 0, -1]

theorem edgeCubic_diagonal (e : P.SingleEdge) :
    (P.edgeCubic e).val.2.2.1 = 0 := by
  funext i
  exact P.diagonalLift_zero_at 0 i rfl

theorem edgeCubic_offDiagonal (e : P.SingleEdge) (b : Edge m) :
    (P.edgeCubic e).val.2.2.2 b = if b = e.val then P.edgeLinear e else 0 := by
  by_cases hb : b = e.val
  · subst b
    simp only [ite_true, eq_self]
    change P.offDiagonalLift 0 0 (fun a => if a = e then 1 else 0) e.val = P.edgeLinear e
    simp [offDiagonalLift, e.property, P.edgeRhs_zero_at 0 e.val 0 rfl rfl, edgeLinear]
  · rw [ite_eq_right hb]
    change P.offDiagonalLift 0 0 (fun a => if a = e then 1 else 0) b = 0
    have hz (h : P.single b = true) : (⟨b, h⟩ : P.SingleEdge) ≠ e :=
      fun h => hb (congrArg Subtype.val h)
    by_cases hs : P.single b = true
    · funext k
      fin_cases k <;> simp [offDiagonalLift, hs, hz hs, P.edgeRhs_zero_at 0 b 0 rfl rfl]
    · funext k
      fin_cases k <;> simp [offDiagonalLift, hs, P.edgeRhs_zero_at 0 b 0 rfl rfl,
        P.edgeRhs_zero_at 0 b 1 rfl rfl, solveTwo]

/-- The lower lift is exactly the graph normal form times its two endpoint variables. -/
theorem traceA_edgeCubic (e : P.SingleEdge) (k : Fin 2) :
    traceA (P.edgeCubic e).val k = C (P.edgeLinear e k) * X e.val.val.1 * X e.val.val.2 := by
  rw [traceA, P.edgeCubic_diagonal]
  let a := e.val.val.1
  let b := e.val.val.2
  have hterm (i j : Fin m) :
      upperCoefficient 0 (P.edgeCubic e).val.2.2.2 i j k =
        if i = a ∧ j = b then P.edgeLinear e k else 0 := by
    by_cases hij : i < j
    · have heq : (⟨(i, j), hij⟩ : Edge m) = e.val ↔ i = a ∧ j = b := by
        rw [Subtype.ext_iff, Prod.mk.injEq]
      rw [show upperCoefficient 0 (P.edgeCubic e).val.2.2.2 i j k =
        (P.edgeCubic e).val.2.2.2 ⟨(i, j), hij⟩ k by simp [upperCoefficient, hij],
        P.edgeCubic_offDiagonal]
      by_cases h : i = a ∧ j = b
      · rw [ite_eq_left (heq.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hh => h (heq.mp hh)), ite_eq_right h]
        rfl
    · have hn : ¬ (i = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩
        exact hij e.val.property
      rw [ite_eq_right hn]
      by_cases h : i = j <;> simp [upperCoefficient, hij, h]
  simp only [traceQuadratic, hterm]
  have hc (i j : Fin m) :
      C (if i = a ∧ j = b then P.edgeLinear e k else 0) * X i * X j =
        if i = a then if j = b then C (P.edgeLinear e k) * X i * X j else 0 else 0 := by
    by_cases hi : i = a <;> by_cases hj : j = b <;> simp [hi, hj]
  simp only [hc, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, a, b]

end IdealGeneration.CubicSupported.Parameters
