module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Evaluation on the paired base points in the quadratic flag

For a pair of coefficients, evaluating the two components at the sum of
its two coordinate points gives `(a + b, c₀ a + c₁ b)`. Distinct parameters
make this an isomorphism. The construction below treats any family of
pairs at once, without a restriction on the number of pairs or on the
characteristic of the field.
-/

noncomputable section
namespace IdealGeneration.QuadraticFlag

variable {K I : Type*} [Field K]

/-- The two evaluation values attached to each pair in a quadratic flag. -/
def pairEvaluation (c₀ c₁ : I → K) : (I → K × K) →ₗ[K] (I → K × K) where
  toFun u i := ((u i).1 + (u i).2, c₀ i * (u i).1 + c₁ i * (u i).2)
  map_add' u v := by ext i <;> simp <;> ring
  map_smul' a u := by ext i <;> simp <;> ring

@[simp] theorem pairEvaluation_apply (c₀ c₁ : I → K) (u : I → K × K) (i : I) :
    pairEvaluation c₀ c₁ u i =
      ((u i).1 + (u i).2, c₀ i * (u i).1 + c₁ i * (u i).2) := rfl

/-- Distinct parameters recover both coefficients in every pair. -/
theorem pairEvaluation_injective (c₀ c₁ : I → K)
    (hc : ∀ i, c₀ i ≠ c₁ i) : Function.Injective (pairEvaluation c₀ c₁) := by
  intro u v huv
  funext i
  have hfirst := congrArg (fun f : I → K × K => (f i).1) huv
  have hsecond := congrArg (fun f : I → K × K => (f i).2) huv
  change (u i).1 + (u i).2 = (v i).1 + (v i).2 at hfirst
  change c₀ i * (u i).1 + c₁ i * (u i).2 =
    c₀ i * (v i).1 + c₁ i * (v i).2 at hsecond
  have hz : (c₀ i - c₁ i) * ((u i).1 - (v i).1) = 0 := by
    linear_combination hsecond - c₁ i * hfirst
  have ha : (u i).1 = (v i).1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (hc i)))
  apply Prod.ext ha
  linear_combination hfirst - ha

/-- Two vanishing values at a paired point force both coefficients to vanish. -/
theorem coefficients_eq_zero_of_pair_equations {c₀ c₁ a b : K}
    (hc : c₀ ≠ c₁) (hfirst : a + b = 0) (hsecond : c₀ * a + c₁ * b = 0) :
    a = 0 ∧ b = 0 := by
  have hz : (c₀ - c₁) * a = 0 := by
    linear_combination hsecond - c₁ * hfirst
  have ha : a = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)
  refine ⟨ha, ?_⟩
  linear_combination hfirst - ha

/-- The paired evaluation is onto, with an explicit interpolation formula. -/
theorem pairEvaluation_surjective (c₀ c₁ : I → K)
    (hc : ∀ i, c₀ i ≠ c₁ i) : Function.Surjective (pairEvaluation c₀ c₁) := by
  intro v
  refine ⟨fun i => ((c₁ i * (v i).1 - (v i).2) / (c₁ i - c₀ i),
    ((v i).2 - c₀ i * (v i).1) / (c₁ i - c₀ i)), ?_⟩
  funext i
  have hd : c₁ i - c₀ i ≠ 0 := sub_ne_zero.mpr (hc i).symm
  apply Prod.ext <;> simp only [pairEvaluation_apply] <;>
    field_simp <;> ring

/-- Paired evaluation is an isomorphism for any number of pairs. -/
def pairEvaluationEquiv (c₀ c₁ : I → K) (hc : ∀ i, c₀ i ≠ c₁ i) :
    (I → K × K) ≃ₗ[K] (I → K × K) :=
  LinearEquiv.ofBijective (pairEvaluation c₀ c₁)
    ⟨pairEvaluation_injective c₀ c₁ hc, pairEvaluation_surjective c₀ c₁ hc⟩

/-- In particular, vanishing at all pair points forces every coefficient to vanish. -/
theorem pairEvaluation_eq_zero_iff (c₀ c₁ : I → K)
    (hc : ∀ i, c₀ i ≠ c₁ i) (u : I → K × K) :
    pairEvaluation c₀ c₁ u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    apply pairEvaluation_injective c₀ c₁ hc
    simpa only [map_zero] using hu
  · rintro rfl
    exact map_zero _

/-- Evaluation at a new coordinate point and at its translates by all
paired base points. The baseline records arbitrary layer corrections. -/
def layerEvaluation (c₀ c₁ : I → K)
    (baseline : (I → K × K) →ₗ[K] (K × K)) :
    (I → K × K) →ₗ[K] ((K × K) × (I → K × K)) where
  toFun u := (baseline u, fun i => baseline u + pairEvaluation c₀ c₁ u i)
  map_add' u v := by
    apply Prod.ext
    · exact map_add _ _ _
    · funext i
      change baseline (u + v) + pairEvaluation c₀ c₁ (u + v) i =
        (baseline u + pairEvaluation c₀ c₁ u i) +
          (baseline v + pairEvaluation c₀ c₁ v i)
      simp only [map_add, Pi.add_apply]
      abel
  map_smul' a u := by
    apply Prod.ext
    · exact map_smul _ _ _
    · funext i
      change baseline (a • u) + pairEvaluation c₀ c₁ (a • u) i =
        a • (baseline u + pairEvaluation c₀ c₁ u i)
      simp only [map_smul, Pi.smul_apply, smul_add]

/-- The coordinate point eliminates the layer correction, after which
paired interpolation recovers every coefficient. -/
theorem layerEvaluation_injective (c₀ c₁ : I → K)
    (hc : ∀ i, c₀ i ≠ c₁ i)
    (baseline : (I → K × K) →ₗ[K] (K × K)) :
    Function.Injective (layerEvaluation c₀ c₁ baseline) := by
  intro u v huv
  have hbase := congrArg Prod.fst huv
  have hpairs := congrArg Prod.snd huv
  apply pairEvaluation_injective c₀ c₁ hc
  funext i
  have hi := congrFun hpairs i
  change baseline u + pairEvaluation c₀ c₁ u i =
    baseline v + pairEvaluation c₀ c₁ v i at hi
  change baseline u = baseline v at hbase
  rw [hbase] at hi
  exact add_left_cancel hi

/-- The allowed evaluation values retain the full dimension of the
coefficient space, independently of the layer corrections. -/
theorem finrank_layerEvaluation_range [Fintype I] (c₀ c₁ : I → K)
    (hc : ∀ i, c₀ i ≠ c₁ i)
    (baseline : (I → K × K) →ₗ[K] (K × K)) :
    Module.finrank K (layerEvaluation c₀ c₁ baseline).range =
      2 * Fintype.card I := by
  rw [LinearMap.finrank_range_of_inj (layerEvaluation_injective c₀ c₁ hc baseline)]
  simp [Module.finrank_pi_fintype, Module.finrank_prod, mul_comm]

/-- The coefficients cancelling the first normal equation and giving the
prescribed value in the second normal equation. -/
def normalCorrection (u₀ v₀ u₁ v₁ target : K) : K × K :=
  (-(v₀ * target) / (u₀ * v₁ - u₁ * v₀),
    u₀ * target / (u₀ * v₁ - u₁ * v₀))

/-- An invertible pair of normal directions admits an explicit correction
with arbitrary prescribed second value and zero first value. -/
theorem normalCorrection_constraints (u₀ v₀ u₁ v₁ target : K)
    (hdet : u₀ * v₁ - u₁ * v₀ ≠ 0) :
    u₀ * (normalCorrection u₀ v₀ u₁ v₁ target).1 +
      v₀ * (normalCorrection u₀ v₀ u₁ v₁ target).2 = 0 ∧
    u₁ * (normalCorrection u₀ v₀ u₁ v₁ target).1 +
      v₁ * (normalCorrection u₀ v₀ u₁ v₁ target).2 = target := by
  constructor <;> dsimp only [normalCorrection] <;> field_simp <;> ring

/-- Existence form of the explicit normal-direction correction. -/
theorem exists_normalCorrection (u₀ v₀ u₁ v₁ target : K)
    (hdet : u₀ * v₁ - u₁ * v₀ ≠ 0) :
    ∃ a b : K, u₀ * a + v₀ * b = 0 ∧ u₁ * a + v₁ * b = target :=
  ⟨(normalCorrection u₀ v₀ u₁ v₁ target).1,
    (normalCorrection u₀ v₀ u₁ v₁ target).2,
    normalCorrection_constraints u₀ v₀ u₁ v₁ target hdet⟩

/-- Invertibility excludes a zero direction in either normal row. -/
theorem normalDirections_ne_zero {u₀ v₀ u₁ v₁ : K}
    (hdet : u₀ * v₁ - u₁ * v₀ ≠ 0) :
    (u₀, v₀) ≠ (0, 0) ∧ (u₁, v₁) ≠ (0, 0) := by
  constructor
  · intro h
    have hu : u₀ = 0 := congrArg Prod.fst h
    have hv : v₀ = 0 := congrArg Prod.snd h
    simp [hu, hv] at hdet
  · intro h
    have hu : u₁ = 0 := congrArg Prod.fst h
    have hv : v₁ = 0 := congrArg Prod.snd h
    simp [hu, hv] at hdet

end IdealGeneration.QuadraticFlag
