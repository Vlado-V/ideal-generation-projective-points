module

public import IdealGeneration.QuadraticFlagLifts
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Core and pair evaluation in the quadratic flag

A lift of the core values can be corrected independently on each
untouched pair. In a single pair, the two layer matrices first resolve
its form coefficients, and the two slopes resolve the normal components.
-/

noncomputable section
namespace IdealGeneration.QuadraticBlockEvaluation
open Module

section Joint

variable {K W C B D P : Type*} [Field K]
  [AddCommGroup W] [Module K W] [AddCommGroup C] [Module K C]
  [AddCommGroup B] [Module K B] [AddCommGroup D] [Module K D]

/-- Evaluate first on the core, then on every untouched pair. -/
def jointEvaluation (e₀ : W →ₗ[K] C) (e : P → W →ₗ[K] B) : W →ₗ[K] (C × (P → B)) :=
  e₀.prod (LinearMap.pi e)

@[simp] theorem jointEvaluation_apply (e₀ : W →ₗ[K] C) (e : P → W →ₗ[K] B) (w : W) :
    jointEvaluation e₀ e w = (e₀ w, fun p => e p w) := rfl

/-- Core interpolation and pair-supported corrections give joint surjectivity. -/
theorem jointEvaluation_surjective [Fintype P]
    (e₀ : W →ₗ[K] C) (e : P → W →ₗ[K] B) (g : P → D →ₗ[K] W)
    (he₀ : Function.Surjective e₀)
    (hcore : ∀ p, e₀.comp (g p) = 0)
    (hoff : ∀ p q, p ≠ q → (e q).comp (g p) = 0)
    (hdiag : ∀ p, Function.Surjective ((e p).comp (g p))) :
    Function.Surjective (jointEvaluation e₀ e) := by
  classical
  rintro ⟨c, b⟩
  obtain ⟨w, hw⟩ := he₀ c
  choose d hd using fun p => hdiag p (b p - e p w)
  refine ⟨w + ∑ p, g p (d p), ?_⟩
  rw [jointEvaluation_apply]
  apply Prod.ext
  · have hzero (p : P) : e₀ (g p (d p)) = 0 := by
      exact congrArg (fun f : D →ₗ[K] C => f (d p)) (hcore p)
    simp [map_sum, hw, hzero]
  · funext q
    change e q (w + ∑ p, g p (d p)) = b q
    rw [map_add, map_sum, Finset.sum_eq_single q]
    · have hq : e q (g q (d q)) = b q - e q w := hd q
      rw [hq]
      abel
    · intro p _ hpq
      exact congrArg (fun f : D →ₗ[K] B => f (d p)) (hoff p q hpq)
    · simp

/-- The target has the core dimension plus one copy of the pair dimension per pair. -/
theorem finrank_jointTarget [Fintype P] [FiniteDimensional K C] [FiniteDimensional K B] :
    finrank K (C × (P → B)) = finrank K C + Fintype.card P * finrank K B := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype]
  simp

/-- The dimension bound makes the surjective joint map bijective. -/
theorem jointEvaluation_bijective [Fintype P] [FiniteDimensional K W]
    [FiniteDimensional K C] [FiniteDimensional K B]
    (e₀ : W →ₗ[K] C) (e : P → W →ₗ[K] B) (g : P → D →ₗ[K] W)
    (he₀ : Function.Surjective e₀)
    (hcore : ∀ p, e₀.comp (g p) = 0)
    (hoff : ∀ p q, p ≠ q → (e q).comp (g p) = 0)
    (hdiag : ∀ p, Function.Surjective ((e p).comp (g p)))
    (hdim : finrank K W ≤ finrank K C + Fintype.card P * finrank K B) :
    Function.Bijective (jointEvaluation e₀ e) := by
  have hs := jointEvaluation_surjective e₀ e g he₀ hcore hoff hdiag
  have hle : finrank K W ≤ finrank K (C × (P → B)) := by
    rw [finrank_jointTarget]
    exact hdim
  have hge := LinearMap.finrank_le_finrank_of_surjective hs
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (le_antisymm hle hge)).mpr hs, hs⟩

end Joint

section Local

variable {K : Type*} [Field K]

/-- The two form coefficients, recorded on both layers. -/
def twoLayerCoefficientMap (L : Bool → Bool → K) : (Bool → K) →ₗ[K] (Bool → K) where
  toFun x j := L j false * x false + L j true * x true
  map_add' x y := by
    funext j
    simp only [Pi.add_apply]
    ring
  map_smul' r x := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem twoLayerCoefficientMap_apply (L : Bool → Bool → K) (x : Bool → K) (j : Bool) :
    twoLayerCoefficientMap L x j = L j false * x false + L j true * x true := rfl

/-- A nonzero two-layer determinant gives arbitrary layer values. -/
theorem twoLayerCoefficientMap_surjective (L : Bool → Bool → K)
    (hL : L false false * L true true - L true false * L false true ≠ 0) :
    Function.Surjective (twoLayerCoefficientMap L) := by
  intro y
  let x := QuadraticElimination.solveLayerNormal
    (L false false, L false true) (L true false, L true true) (y false) (y true)
  have hx := QuadraticElimination.solveLayerNormal_spec
    (L false false, L false true) (L true false, L true true) (y false) (y true) hL
  refine ⟨fun r => if r then x.2 else x.1, ?_⟩
  funext j
  cases j
  · exact hx.1
  · exact hx.2

/-- The signed layer coefficients of the even and odd forms. -/
def signedLayerCoordinates (L : Bool → Bool → Bool → K) :
    (Bool × Bool → K) →ₗ[K] (Bool → K × K) where
  toFun x j := (twoLayerCoefficientMap (L false) (fun r => x (false, r)) j,
    -twoLayerCoefficientMap (L true) (fun r => x (true, r)) j)
  map_add' x y := by
    funext j
    apply Prod.ext <;> simp [mul_add] <;> ring
  map_smul' r x := by
    funext j
    apply Prod.ext <;> simp [smul_eq_mul] <;> ring

/-- The two layer systems act independently on the even and odd forms. -/
theorem signedLayerCoordinates_surjective (L : Bool → Bool → Bool → K)
    (hL : ∀ i, L i false false * L i true true - L i true false * L i false true ≠ 0) :
    Function.Surjective (signedLayerCoordinates L) := by
  intro y
  obtain ⟨x₀, hx₀⟩ := twoLayerCoefficientMap_surjective (L false) (hL false)
    (fun j => (y j).1)
  obtain ⟨x₁, hx₁⟩ := twoLayerCoefficientMap_surjective (L true) (hL true)
    (fun j => -(y j).2)
  refine ⟨fun p => if p.1 then x₁ p.2 else x₀ p.2, ?_⟩
  funext j
  apply Prod.ext
  · exact congrFun hx₀ j
  · change -twoLayerCoefficientMap (L true) x₁ j = (y j).2
    rw [congrFun hx₁ j, neg_neg]

/-- The four forms of one untouched pair evaluated at its two layer probes. -/
def localBlockEvaluation (c₀ c₁ : K) (L : Bool → Bool → Bool → K) :
    (Bool × Bool → K) →ₗ[K] (Bool → K × K) :=
  (QuadraticFlag.pairEvaluation (fun _ : Bool => c₁) (fun _ : Bool => c₀)).comp
    (signedLayerCoordinates L)

/-- The actual value is the odd normal vector times the even coefficient,
minus the even normal vector times the odd coefficient. -/
theorem localBlockEvaluation_apply (c₀ c₁ : K) (L : Bool → Bool → Bool → K)
    (x : Bool × Bool → K) (j : Bool) :
    localBlockEvaluation c₀ c₁ L x j =
      (∑ r : Bool, x (false, r) * L false j r) • ((1, c₁) : K × K) -
      (∑ r : Bool, x (true, r) * L true j r) • ((1, c₀) : K × K) := by
  apply Prod.ext <;>
    simp [localBlockEvaluation, signedLayerCoordinates, Fintype.univ_bool, smul_eq_mul] <;> ring

/-- Independent slopes and both nonzero layer determinants make the four-block onto. -/
theorem localBlockEvaluation_surjective (c₀ c₁ : K) (L : Bool → Bool → Bool → K)
    (hc : c₀ ≠ c₁)
    (hL : ∀ i, L i false false * L i true true - L i true false * L i false true ≠ 0) :
    Function.Surjective (localBlockEvaluation c₀ c₁ L) :=
  (QuadraticFlag.pairEvaluation_surjective (fun _ : Bool => c₁)
    (fun _ : Bool => c₀) (fun _ => hc.symm)).comp (signedLayerCoordinates_surjective L hL)

end Local

section Untouched

variable {K P W : Type*} [Field K] [Fintype P] [DecidableEq P]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Three core probes and two probes per remaining pair have total dimension `2h+2`. -/
theorem finrank_coreUntouchedTarget (p₀ : P) :
    finrank K ((Fin 3 → K × K) × ({p : P // p ≠ p₀} → Bool → K × K)) =
      2 * Fintype.card (P × Bool) + 2 := by
  have hcore : finrank K (Fin 3 → K × K) = 6 := by simp [Module.finrank_pi_fintype]
  have hpair : finrank K (Bool → K × K) = 4 := by simp [Module.finrank_pi_fintype]
  rw [finrank_jointTarget, hcore, hpair, Fintype.card_prod, Fintype.card_bool]
  have hcard : Fintype.card {p : P // p ≠ p₀} = Fintype.card P - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun p : P => p = p₀))
  rw [hcard]
  have hpos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨p₀⟩
  omega

/-- The bound for the actual eliminated space is exactly the dimension needed
for joint interpolation on the core and the untouched pairs. -/
theorem coreUntouchedEvaluation_bijective (p₀ : P)
    (e₀ : W →ₗ[K] (Fin 3 → K × K)) (e : {p : P // p ≠ p₀} → W →ₗ[K] (Bool → K × K))
    (g : {p : P // p ≠ p₀} → (Bool × Bool → K) →ₗ[K] W)
    (he₀ : Function.Surjective e₀)
    (hcore : ∀ p, e₀.comp (g p) = 0)
    (hoff : ∀ p q, p ≠ q → (e q).comp (g p) = 0)
    (hdiag : ∀ p, Function.Surjective ((e p).comp (g p)))
    (hdim : finrank K W ≤ 2 * Fintype.card (P × Bool) + 2) :
    Function.Bijective (jointEvaluation e₀ e) := by
  apply jointEvaluation_bijective e₀ e g he₀ hcore hoff hdiag
  rw [← finrank_jointTarget, finrank_coreUntouchedTarget p₀]
  exact hdim

end Untouched
end IdealGeneration.QuadraticBlockEvaluation
