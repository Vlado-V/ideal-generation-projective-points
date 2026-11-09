module

public import IdealGeneration.CubicSupportedRestriction
public import IdealGeneration.CubicExplicitSource

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Restriction of the independent coordinates and the actual cubic map in B.4. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Compatible

open CubicUpperSolve CubicUpperBlockEquations CubicMiddle CubicNormalExpansion MvPolynomial
open QuadraticTraceRestriction (restrictPolynomial restrict_X_embedded eval_restrict)

variable {K : Type*} [Field K] {m : ℕ}
variable {P : Parameters K m} {Q : Parameters K (m + 2)} (h : Compatible P Q)

/-- The normal pair restricts to the old cubic kernel and retains its quartic equation. -/
def restrictOmega : Omega Q.cubicTop →ₗ[K] Omega P.cubicTop where
  toFun x := ⟨(h.restrictKernel x.val.1, h.restrictKernel x.val.2), x.property⟩
  map_add' _ _ := Subtype.ext (Prod.ext (map_add h.restrictKernel _ _) (map_add h.restrictKernel _ _))
  map_smul' _ _ := Subtype.ext (Prod.ext (map_smul h.restrictKernel _ _) (map_smul h.restrictKernel _ _))

theorem restrictOmega_surjective : Function.Surjective h.restrictOmega := by
  intro x
  obtain ⟨u, hu⟩ := h.restrictKernel_surjective x.val.1
  obtain ⟨v, hv⟩ := h.restrictKernel_surjective x.val.2
  have hmem : (u, v) ∈ Omega Q.cubicTop := by
    change (h.restrictKernel u, h.restrictKernel v) ∈ Omega P.cubicTop
    rw [hu, hv]
    exact x.property
  exact ⟨⟨(u, v), hmem⟩, Subtype.ext (Prod.ext hu hv)⟩

/-- Retain the old independent normal, antisymmetric and single-edge coordinates. -/
def restrictParameters : Q.EliminatedParameters →ₗ[K] P.EliminatedParameters where
  toFun x := (h.restrictOmega x.1, (fun e => x.2.1 (oldEdge m e)),
    fun i e => x.2.2 (Fin.castAdd 2 i) (h.singleEdge e))
  map_add' _ _ := Prod.ext (map_add h.restrictOmega _ _) rfl
  map_smul' _ _ := Prod.ext (map_smul h.restrictOmega _ _) rfl

/-- Restriction is onto by extending the two independent arrays by zero. -/
theorem restrictParameters_surjective : Function.Surjective h.restrictParameters := by
  intro x
  obtain ⟨w, hw⟩ := h.restrictOmega_surjective x.1
  let z : Edge (m + 2) → Fin 3 → K := Function.extend (oldEdge m) x.2.1 0
  let g : Fin m → Q.SingleEdge → K := fun i => Function.extend h.singleEdge (x.2.2 i) 0
  let r : Fin (m + 2) → Q.SingleEdge → K := extendTrace g
  refine ⟨(w, z, r), Prod.ext hw (Prod.ext ?_ ?_)⟩
  · funext e
    exact (oldEdge m).injective.extend_apply _ _ e
  · funext i e
    change r (Fin.castAdd 2 i) (h.singleEdge e) = x.2.2 i e
    rw [show r (Fin.castAdd 2 i) = g i from extendTrace_old g i]
    exact h.singleEdge.injective.extend_apply _ _ e

private theorem antisymmetric_old (z : Edge (m + 2) → Fin 3 → K)
    (i j : Fin m) (a : Fin 3) :
    antisymmetric z (Fin.castAdd 2 i) (Fin.castAdd 2 j) a =
      antisymmetric (fun e => z (oldEdge m e)) i j a := by
  have hlt (i j : Fin m) : Fin.castAdd 2 i < Fin.castAdd 2 j ↔ i < j := Iff.rfl
  by_cases hij : i < j
  · simp [antisymmetric, hij, (hlt i j).mpr hij]
    rfl
  · by_cases hji : j < i
    · simp [antisymmetric, hij, hji, (hlt i j).not.mpr hij, (hlt j i).mpr hji]
      rfl
    · simp [antisymmetric, hij, hji, (hlt i j).not.mpr hij, (hlt j i).not.mpr hji]

private theorem quadraticTarget_old (U V : Coefficients K (m + 2)) (i j : Fin m) (a : Fin 3) :
    quadraticTarget U V (Fin.castAdd 2 i) (Fin.castAdd 2 j) a =
      quadraticTarget (restrictCoefficients U) (restrictCoefficients V) i j a := by
  fin_cases a <;> simp [quadraticTarget, restrictCoefficients, upperCoefficient_old]

private theorem freeCoefficients_lift {n : ℕ} (R : Parameters K n)
    (C : Fin 4 → K) (B : Fin n → Fin 3 → K) (z : R.SingleEdge → K) (e : R.SingleEdge) :
    R.freeCoefficients (R.coefficientLift C B z) e = z e := by
  change -R.offDiagonalLift C B z e.val 1 = z e
  simp [Parameters.offDiagonalLift, e.property]

private theorem restrictKernel_coefficientLift (C : Fin 4 → K)
    (B : Fin (m + 2) → Fin 3 → K) (z : Q.SingleEdge → K) :
    h.restrictKernel (Q.coefficientLift C B z) =
      P.coefficientLift C (fun i => B (Fin.castAdd 2 i)) (fun e => z (h.singleEdge e)) := by
  apply P.kernelCoordinatesEquiv.injective
  change (C, (fun i => B (Fin.castAdd 2 i)), P.freeCoefficients (h.restrictKernel (Q.coefficientLift C B z))) =
    (C, (fun i => B (Fin.castAdd 2 i)),
      P.freeCoefficients (P.coefficientLift C (fun i => B (Fin.castAdd 2 i))
        (fun e => z (h.singleEdge e))))
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext e
  change P.freeCoefficients (h.restrictKernel (Q.coefficientLift C B z)) e =
    P.freeCoefficients (P.coefficientLift C (fun i => B (Fin.castAdd 2 i))
      (fun e => z (h.singleEdge e))) e
  rw [h.freeCoefficients_restrictKernel, freeCoefficients_lift, freeCoefficients_lift]

/-- The cubic for any old trace multiplier restricts to the old explicit solve. -/
theorem parameterTraceCubic_restrict (x : Q.EliminatedParameters) (i : Fin m) :
    h.restrictKernel (Q.parameterTraceCubic x (Fin.castAdd 2 i)) =
      P.parameterTraceCubic (h.restrictParameters x) i := by
  rw [Parameters.parameterTraceCubic, h.restrictKernel_coefficientLift]
  unfold Parameters.parameterTraceCubic
  dsimp only [restrictParameters, restrictOmega]
  congr 2
  funext j a
  change symmetricCompletion (quadraticTarget x.1.val.1.val x.1.val.2.val) x.2.1
      (Fin.castAdd 2 i) (Fin.castAdd 2 j) a =
    symmetricCompletion (quadraticTarget (restrictCoefficients x.1.val.1.val)
      (restrictCoefficients x.1.val.2.val)) (fun e => x.2.1 (oldEdge m e)) i j a
  simp only [symmetricCompletion, antisymmetric_old, quadraticTarget_old]

private theorem eval_traceA (u : Coefficients K m) (k : Fin 2) (y : Fin m → K) :
    eval y (traceA u k) = traceQuadratic (fun i j => upperCoefficient u.2.2.1 u.2.2.2 i j k) y := by
  simp [traceA, traceQuadratic, map_sum]

private theorem eval_traceA_extendTrace (u : Coefficients K (m + 2)) (k : Fin 2) (y : Fin m → K) :
    eval (extendTrace y) (traceA u k) = eval y (traceA (restrictCoefficients u) k) := by
  rw [eval_traceA, eval_traceA]
  simp only [traceQuadratic, Fin.sum_univ_add, extendTrace_old, extendTrace_new, upperCoefficient_old,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, restrictCoefficients, LinearMap.coe_mk,
    AddHom.coe_mk]

variable {f g : ℕ} (free : Fin f → Fin m → K) (free' : Fin g → Fin (m + 2) → K)
variable (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

/-- Evaluating the actual explicit cubic map on the old space commutes with restriction. -/
theorem parameterPhi_eval_extendTrace (x : Q.EliminatedParameters) (k : Fin 2) (y : Fin m → K) :
    eval (extendTrace y) (Q.parameterPhi free' h₂ h₆ x k).val =
      eval y (P.parameterPhi free h₂ h₆ (h.restrictParameters x) k).val := by
  rw [Q.parameterPhi_polynomial, P.parameterPhi_polynomial]
  simp only [productNormal1, map_sum, map_add, map_mul, eval_X, Fin.sum_univ_add,
    extendTrace_old, extendTrace_new, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_traceA_extendTrace, ← h.restrictKernel_val, h.parameterTraceCubic_restrict]

/-- Every new parameter column vanishes on the old trace space. -/
theorem parameterPhi_eval_extendTrace_of_mem_ker
    (x : h.restrictParameters.ker) (k : Fin 2) (y : Fin m → K) :
    eval (extendTrace y) (Q.parameterPhi free' h₂ h₆ x.val k).val = 0 := by
  rw [h.parameterPhi_eval_extendTrace (fun i : Fin 0 => i.elim0) free' h₂ h₆ x.val k y,
    LinearMap.mem_ker.mp x.property, map_zero]
  exact map_zero (eval y)

end IdealGeneration.CubicSupported.Compatible
