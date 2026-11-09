module

public import IdealGeneration.CubicExplicitSource
public import IdealGeneration.CubicLiftDecomposition
public import IdealGeneration.CubicSupportedRestriction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The star-supported columns in the last two families of Appendix B.7. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Parameters

open MvPolynomial CubicNormalExpansion CubicUpperSolve CubicUpperBlockEquations

variable {K : Type*} [Field K] {m : ℕ} (P : Parameters K m)

/-- Multiply a binary linear form by normal coordinate `u`, in descending `s` order. -/
def shiftLinear (u : Fin 2) (a : Fin 2 → K) : Fin 3 → K :=
  if u = 0 then ![a 0, a 1, 0] else ![0, a 0, a 1]

/-- Multiply a binary quadratic by normal coordinate `u`, in descending `s` order. -/
def shiftQuadratic (u : Fin 2) (a : Fin 3 → K) : Fin 4 → K :=
  if u = 0 then ![a 0, a 1, a 2, 0] else ![0, a 0, a 1, a 2]

@[simp] theorem shiftLinear_zero (u : Fin 2) : shiftLinear u (0 : Fin 2 → K) = 0 := by
  funext q
  fin_cases u <;> fin_cases q <;> simp [shiftLinear]

@[simp] theorem shiftQuadratic_zero (u : Fin 2) : shiftQuadratic u (0 : Fin 3 → K) = 0 := by
  funext q
  fin_cases u <;> fin_cases q <;> simp [shiftQuadratic]

/-- The negative of the selected cubic occupies the chosen normal multiplier. -/
def starNormalPair (u : Fin 2) (F : P.coefficientKernel) :
    P.coefficientKernel × P.coefficientKernel :=
  if u = 0 then (-F, 0) else (0, -F)

/-- The resulting quadratic target for the trace multipliers. -/
def starTarget (u : Fin 2) (F : P.coefficientKernel) : Fin m → Fin m → Fin 3 → K :=
  quadraticTarget (P.starNormalPair u F).1.val (P.starNormalPair u F).2.val

/-- Put the required mixed coefficient at the center of each trace multiplier. -/
def starMixed (u : Fin 2) (w : Fin m) (a : Fin m → Fin 2 → K) : Fin m → Fin m → Fin 3 → K :=
  fun i => mixedArray w (shiftLinear u (a i))

private theorem upperCoefficient_zero (i j : Fin m) (k : Fin 2) :
    upperCoefficient (0 : Fin m → Fin 2 → K) 0 i j k = 0 := by
  by_cases h : i < j
  · simp [upperCoefficient, h]
  · simp [upperCoefficient, h]

private theorem upperCoefficient_neg (d : Fin m → Fin 2 → K) (b : Edge m → Fin 2 → K)
    (i j : Fin m) (k : Fin 2) :
    upperCoefficient (-d) (-b) i j k = -upperCoefficient d b i j k := by
  by_cases h : i < j
  · simp [upperCoefficient, h]
  · by_cases h' : i = j <;> simp [upperCoefficient, h, h']

private theorem starTarget_entry (u : Fin 2) (F : P.coefficientKernel) (i j : Fin m) (q : Fin 3) :
    P.starTarget u F i j q =
      -shiftLinear u (fun k => upperCoefficient F.val.2.2.1 F.val.2.2.2 i j k) q := by
  fin_cases u <;> fin_cases q <;>
    simp [starTarget, starNormalPair, shiftLinear, quadraticTarget, upperCoefficient_zero,
      upperCoefficient_neg]

private theorem traceQuadratic_starMixed (u : Fin 2) (w : Fin m) (a : Fin m → Fin 2 → K)
    (q : Fin 3) (y : Fin m → K) :
    traceQuadratic (fun i j => starMixed u w a i j q) y =
      y w * ∑ i, shiftLinear u (a i) q * y i := by
  rw [traceQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single w]
  · simp only [starMixed, mixedArray, ite_true]
    ring
  · intro j _ hj
    simp [starMixed, mixedArray, hj]
  · simp

private theorem traceQuadratic_starTarget (u : Fin 2) (F : P.coefficientKernel)
    (w : Fin m) (a : Fin m → Fin 2 → K)
    (hD : F.val.2.2.1 = starDiagonal w a) (hE : F.val.2.2.2 = starOffDiagonal w a)
    (q : Fin 3) (y : Fin m → K) :
    traceQuadratic (fun i j => P.starTarget u F i j q) y =
      -(y w * ∑ i, shiftLinear u (a i) q * y i) := by
  have hneg (A : Fin m → Fin m → K) :
      traceQuadratic (fun i j => -A i j) y = -traceQuadratic A y := by
    simp only [traceQuadratic, neg_mul, Finset.sum_neg_distrib]
  have hzero : traceQuadratic (fun _ _ : Fin m => (0 : K)) y = 0 := by
    simp [traceQuadratic]
  simp_rw [P.starTarget_entry, hD, hE]
  rw [hneg]
  fin_cases u <;> fin_cases q <;> simp [shiftLinear, traceQuadratic_star, hzero]

/-- The free antisymmetric array is read from the desired mixed coefficients on increasing edges. -/
def starAntisymmetric (u : Fin 2) (F : P.coefficientKernel) (w : Fin m)
    (a : Fin m → Fin 2 → K) : Edge m → Fin 3 → K :=
  fun e q => starMixed u w a e.val.1 e.val.2 q +
    (P.starTarget u F e.val.1 e.val.2 q + P.starTarget u F e.val.2 e.val.1 q) / 2

/-- The prescribed center coefficients solve the actual symmetric-completion equations. -/
theorem starMixed_eq_completion (h₂ : (2 : K) ≠ 0) (u : Fin 2) (F : P.coefficientKernel)
    (w : Fin m) (a : Fin m → Fin 2 → K)
    (hD : F.val.2.2.1 = starDiagonal w a) (hE : F.val.2.2.2 = starOffDiagonal w a) :
    starMixed u w a = symmetricCompletion (P.starTarget u F) (P.starAntisymmetric u F w a) := by
  obtain ⟨z, hz⟩ := symmetricCompletion_complete h₂ (P.starTarget u F) (starMixed u w a) (by
    intro q y
    rw [traceQuadratic_starMixed, P.traceQuadratic_starTarget u F w a hD hE, add_neg_cancel])
  have hz' : z = P.starAntisymmetric u F w a := by
    funext e q
    have he := congrFun (congrFun (congrFun hz e.val.1) e.val.2) q
    simp only [symmetricCompletion, antisymmetric, dite_eq_left e.property] at he
    unfold starAntisymmetric
    exact (sub_eq_iff_eq_add.mp he.symm)
  rwa [← hz']

private theorem starCorrection (u : Fin 2) (F : P.coefficientKernel) (i : Fin m) :
    cubicCorrection ((P.starNormalPair u F).1.val.2.1 i)
      ((P.starNormalPair u F).2.val.2.1 i) = shiftQuadratic u (F.val.2.1 i) := by
  funext q
  fin_cases u <;> fin_cases q <;>
    simp [starNormalPair, shiftQuadratic, cubicCorrection, QuadraticElimination.normalCubicMap]

private theorem starNormalPair_mem_omega (u : Fin 2) (F : P.coefficientKernel)
    (hC : F.val.1 = 0) : P.starNormalPair u F ∈ Omega P.cubicTop := by
  have htop : P.cubicTop F = 0 := hC
  have hs : P.cubicTop (P.starNormalPair u F).1 = 0 := by
    fin_cases u <;> simp [starNormalPair, htop]
  have ht : P.cubicTop (P.starNormalPair u F).2 = 0 := by
    fin_cases u <;> simp [starNormalPair, htop]
  rw [LinearMap.mem_ker]
  change normalQuarticMap (P.cubicTop (P.starNormalPair u F).1,
    P.cubicTop (P.starNormalPair u F).2) = 0
  rw [hs, ht]
  exact map_zero normalQuarticMap

/-- The star column in the independent eliminated parameter coordinates. -/
def starParameter (u : Fin 2) (F : P.coefficientKernel) (hC : F.val.1 = 0)
    (w : Fin m) (a : Fin m → Fin 2 → K) : P.EliminatedParameters :=
  (⟨P.starNormalPair u F, P.starNormalPair_mem_omega u F hC⟩,
    P.starAntisymmetric u F w a, 0)

/-- Each actual trace multiplier consists of its forced pure lift and the centered mixed lift. -/
theorem parameterTraceCubic_star (h₂ : (2 : K) ≠ 0) (u : Fin 2)
    (F : P.coefficientKernel) (hC : F.val.1 = 0) (w : Fin m) (a : Fin m → Fin 2 → K)
    (hD : F.val.2.2.1 = starDiagonal w a) (hE : F.val.2.2.2 = starOffDiagonal w a) (i : Fin m) :
    P.parameterTraceCubic (P.starParameter u F hC w a) i =
      P.pureCubic (shiftQuadratic u (F.val.2.1 i)) +
        P.mixedCubic w (shiftLinear u (a i)) := by
  change P.coefficientLift (cubicCorrection ((P.starNormalPair u F).1.val.2.1 i)
    ((P.starNormalPair u F).2.val.2.1 i))
      (symmetricCompletion (P.starTarget u F) (P.starAntisymmetric u F w a) i) 0 = _
  rw [P.starCorrection, ← P.starMixed_eq_completion h₂ u F w a hD hE]
  apply P.kernelCoordinatesEquiv.injective
  simp [starMixed, pureCubic, mixedCubic]

private theorem traceA_add (U V : Coefficients K m) (k : Fin 2) :
    traceA (U + V) k = traceA U k + traceA V k :=
  (traceALinear k).map_add U V

/-- The star parameter gives the literal pure and mixed trace polynomials. -/
theorem parameterPhi_star {f : ℕ} (free : Fin f → Fin m → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (u : Fin 2)
    (F : P.coefficientKernel) (hC : F.val.1 = 0) (w : Fin m) (a : Fin m → Fin 2 → K)
    (hD : F.val.2.2.1 = starDiagonal w a) (hE : F.val.2.2.2 = starOffDiagonal w a) (k : Fin 2) :
    (P.parameterPhi free h₂ h₆ (P.starParameter u F hC w a) k).val =
      (∑ i, X i * traceA (P.pureCubic (shiftQuadratic u (F.val.2.1 i))).val k) +
        X w * ∑ i, X i * ∑ j, C (P.mixedLinear w (shiftLinear u (a i)) j k) * X j := by
  rw [P.parameterPhi_polynomial, productNormal1]
  simp_rw [P.parameterTraceCubic_star h₂ u F hC w a hD hE]
  change (∑ i, X i * traceA ((P.pureCubic (shiftQuadratic u (F.val.2.1 i))).val +
    (P.mixedCubic w (shiftLinear u (a i))).val) k) = _
  simp only [traceA_add, P.traceA_mixedCubic, mul_add, Finset.sum_add_distrib]
  congr 1
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An increasing edge with prescribed endpoints in either order. -/
def joins (e : Edge m) (i w : Fin m) : Prop := e.val = (i, w) ∨ e.val = (w, i)

private theorem joins_ne {e : Edge m} {i w : Fin m} (h : joins e i w) : i ≠ w := by
  rintro rfl
  rcases h with h | h <;> have hlt := e.property <;> rw [h] at hlt <;> exact lt_irrefl _ hlt

private theorem eq_of_joins {e b : Edge m} {i w : Fin m}
    (he : joins e i w) (hb : joins b i w) : e = b := by
  apply Subtype.ext
  have he' := e.property
  have hb' := b.property
  rcases he with he | he <;> rcases hb with hb | hb <;> rw [he, hb] <;>
    first | rfl | rw [he] at he'; rw [hb] at hb'; exact (lt_asymm he' hb').elim

/-- The single-edge lift has only the coefficient of its other endpoint in the star. -/
def edgeStarLinear (e : P.SingleEdge) (i : Fin m) : Fin m → Fin 2 → K :=
  fun j => if j = i then P.edgeLinear e else 0

private theorem edgeCubic_starDiagonal (e : P.SingleEdge) (i w : Fin m) (h : joins e.val i w) :
    (P.edgeCubic e).val.2.2.1 = starDiagonal w (P.edgeStarLinear e i) := by
  rw [P.edgeCubic_diagonal]
  funext j k
  by_cases hj : j = w
  · subst j
    simp [starDiagonal, edgeStarLinear, Ne.symm (joins_ne h)]
  · simp [starDiagonal, hj]

private theorem edgeCubic_starOffDiagonal (e : P.SingleEdge) (i w : Fin m)
    (h : joins e.val i w) :
    (P.edgeCubic e).val.2.2.2 = starOffDiagonal w (P.edgeStarLinear e i) := by
  funext b k
  rw [P.edgeCubic_offDiagonal]
  by_cases hb : b = e.val
  · subst b
    have hiw := joins_ne h
    rcases h with h | h <;> simp [starOffDiagonal, edgeStarLinear, h, hiw]
  · by_cases h1 : b.val.1 = w
    · have hn : b.val.2 ≠ i := fun h2 => hb (eq_of_joins (Or.inr (Prod.ext h1 h2)) h)
      simp [starOffDiagonal, edgeStarLinear, hb, h1, hn]
    · by_cases h2 : b.val.2 = w
      · have hn : b.val.1 ≠ i := fun h1' => hb (eq_of_joins (Or.inl (Prod.ext h1' h2)) h)
        simp [starOffDiagonal, edgeStarLinear, hb, h1, h2, hn]
      · simp [starOffDiagonal, hb, h1, h2]

private theorem pureCubic_zero : P.pureCubic (0 : Fin 4 → K) = 0 := by
  rw [pureCubic, P.coefficientLift_eq_symm]
  exact map_zero P.kernelCoordinatesEquiv.symm

private theorem mixedCubic_zero (w : Fin m) : P.mixedCubic w (0 : Fin 3 → K) = 0 := by
  have h : mixedArray w (0 : Fin 3 → K) = 0 := by
    funext j
    simp [mixedArray]
  rw [mixedCubic, h, P.coefficientLift_eq_symm]
  exact map_zero P.kernelCoordinatesEquiv.symm

private theorem mixedLinear_zero (w : Fin m) : P.mixedLinear w (0 : Fin 3 → K) = 0 := by
  funext j
  simp [mixedLinear, P.mixedCubic_zero]

private theorem traceA_zero (k : Fin 2) : traceA (0 : Coefficients K m) k = 0 :=
  map_zero (traceALinear k)

/-- The parameter for a single edge through the new coordinate. -/
def edgeStarParameter (u : Fin 2) (e : P.SingleEdge) (i w : Fin m) : P.EliminatedParameters :=
  P.starParameter u (P.edgeCubic e) rfl w (P.edgeStarLinear e i)

/-- The fourth family in B.7 before setting the new trace variables to zero. -/
def edgeStarRemainder (u : Fin 2) (e : P.SingleEdge) (i w : Fin m) (k : Fin 2) : Poly K m :=
  X i * ∑ j, C (P.mixedLinear w (shiftLinear u (P.edgeLinear e)) j k) * X j

theorem parameterPhi_edgeStar {f : ℕ} (free : Fin f → Fin m → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (u : Fin 2)
    (e : P.SingleEdge) (i w : Fin m) (h : joins e.val i w) (k : Fin 2) :
    (P.parameterPhi free h₂ h₆ (P.edgeStarParameter u e i w) k).val =
      X w * P.edgeStarRemainder u e i w k := by
  unfold edgeStarParameter
  rw [P.parameterPhi_star free h₂ h₆ u (P.edgeCubic e) rfl w (P.edgeStarLinear e i)
    (P.edgeCubic_starDiagonal e i w h) (P.edgeCubic_starOffDiagonal e i w h)]
  rw [show (P.edgeCubic e).val.2.1 = 0 from rfl]
  simp only [Pi.zero_apply, shiftQuadratic_zero, P.pureCubic_zero, Submodule.coe_zero,
    traceA_zero, mul_zero, Finset.sum_const_zero, zero_add]
  apply congrArg (fun z => X w * z)
  rw [Finset.sum_eq_single i]
  · simp [edgeStarRemainder, edgeStarLinear]
  · intro j _ hj
    simp [edgeStarLinear, hj, P.mixedLinear_zero]
  · simp

/-- The parameter for a mixed lift centered at the new coordinate. -/
def mixedStarParameter (u : Fin 2) (w : Fin m) (Q : Fin 3 → K) : P.EliminatedParameters :=
  P.starParameter u (P.mixedCubic w Q) rfl w (P.mixedLinear w Q)

/-- The fifth family in B.7 before setting the new trace variables to zero. -/
def mixedStarRemainder (u : Fin 2) (w : Fin m) (Q : Fin 3 → K) (k : Fin 2) : Poly K m :=
  traceA (P.pureCubic (shiftQuadratic u Q)).val k +
    ∑ i, X i * ∑ j, C (P.mixedLinear w (shiftLinear u (P.mixedLinear w Q i)) j k) * X j

theorem parameterPhi_mixedStar {f : ℕ} (free : Fin f → Fin m → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (u : Fin 2)
    (w : Fin m) (Q : Fin 3 → K) (k : Fin 2) :
    (P.parameterPhi free h₂ h₆ (P.mixedStarParameter u w Q) k).val =
      X w * P.mixedStarRemainder u w Q k := by
  unfold mixedStarParameter
  rw [P.parameterPhi_star free h₂ h₆ u (P.mixedCubic w Q) rfl w (P.mixedLinear w Q)
    (P.mixedCubic_diagonal w Q) (P.mixedCubic_offDiagonal w Q)]
  rw [show (P.mixedCubic w Q).val.2.1 = mixedArray w Q from rfl,
    Finset.sum_eq_single w]
  · simp only [mixedArray, ite_true, mixedStarRemainder]
    ring
  · intro i _ hi
    simp [mixedArray, hi, P.pureCubic_zero, traceA_zero]
  · simp

section OldTrace

open QuadraticTraceRestriction (restrictPolynomial restrict_X_embedded restrict_X_off
  restrict_linearPolynomial)

variable {n : ℕ}

local notation "oldTrace" => (Fin.castAddEmb 2 : Fin n ↪ Fin (n + 2))

private theorem restrict_traceX_old (i : Fin n) :
    restrictPolynomial K oldTrace (X (Fin.castAdd 2 i)) = X i :=
  restrict_X_embedded K oldTrace i

private theorem restrict_traceX_new (j : Fin 2) :
    restrictPolynomial K oldTrace (X (Fin.natAdd n j)) = 0 := by
  apply restrict_X_off
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  change i.val = n + j.val at he
  omega

private theorem restrict_traceLinear (a : Fin (n + 2) → K) :
    restrictPolynomial K oldTrace (∑ j, C (a j) * X j) =
      ∑ j : Fin n, C (a (Fin.castAdd 2 j)) * X j :=
  restrict_linearPolynomial K oldTrace a

private theorem restrict_traceA (U : Coefficients K (n + 2)) (k : Fin 2) :
    restrictPolynomial K oldTrace (traceA U k) = traceA (restrictCoefficients U) k := by
  simp only [traceA, traceQuadratic, map_sum, map_mul, MvPolynomial.algHom_C]
  simp only [Fin.sum_univ_add, restrict_traceX_old, restrict_traceX_new, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, upperCoefficient_old]
  rfl

/-- Setting the new variables to zero after extracting `X w` gives the fourth B.7 family. -/
theorem restrict_edgeStarRemainder (R : Parameters K (n + 2)) (u : Fin 2)
    (e : R.SingleEdge) (i : Fin n) (w : Fin (n + 2)) (k : Fin 2) :
    restrictPolynomial K oldTrace (R.edgeStarRemainder u e (Fin.castAdd 2 i) w k) =
      X i * ∑ j : Fin n, C (R.mixedLinear w (shiftLinear u (R.edgeLinear e))
        (Fin.castAdd 2 j) k) * X j := by
  rw [edgeStarRemainder, map_mul, restrict_traceX_old, restrict_traceLinear]

/-- Setting the new variables to zero after extracting `X w` gives the fifth B.7 family. -/
theorem restrict_mixedStarRemainder (R : Parameters K (n + 2)) (u : Fin 2)
    (w : Fin (n + 2)) (Q : Fin 3 → K) (k : Fin 2) :
    restrictPolynomial K oldTrace (R.mixedStarRemainder u w Q k) =
      traceA (restrictCoefficients (R.pureCubic (shiftQuadratic u Q)).val) k +
      ∑ i : Fin n, X i * ∑ j : Fin n, C (R.mixedLinear w
        (shiftLinear u (R.mixedLinear w Q (Fin.castAdd 2 i))) (Fin.castAdd 2 j) k) * X j := by
  rw [mixedStarRemainder, map_add, restrict_traceA, map_sum, Fin.sum_univ_add]
  simp only [map_mul, restrict_traceX_old, restrict_traceX_new, zero_mul,
    Finset.sum_const_zero, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [restrict_traceLinear]

end OldTrace

end IdealGeneration.CubicSupported.Parameters
