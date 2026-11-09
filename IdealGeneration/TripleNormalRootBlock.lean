module

public import IdealGeneration.TripleNormalChordPlane
public import IdealGeneration.TripleNormalRootMotion

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Normalization of the nine root–new coefficient blocks. -/

noncomputable section
namespace IdealGeneration.TripleNormal

open Matrix
open scoped Matrix

variable {K : Type*} [Field K]

abbrev RootBlockInput (K : Type*) :=
  (Fin 3 → Fin 3 → K) × (Fin 3 → Fin 3 → Fin 2 → K)

abbrev RootBlockOutput (K : Type*) := Fin 3 → Fin 3 → Fin 3 → K

private def motionLinear (v : Fin 3 → K) : (Fin 3 → K) →ₗ[K] Forms K 3 2 where
  toFun u := motionQuadratic u v
  map_add' u w := by
    apply Subtype.ext
    simp [motionQuadratic, add_mul]
  map_smul' a u := by
    apply Subtype.ext
    simp [motionQuadratic]

/-- Each root–new coefficient is its endpoint-plane contribution minus the local lift. -/
def rootBlockMap (ω : K) (roots b : Fin 3 → K) : RootBlockInput K →ₗ[K] RootBlockOutput K where
  toFun f r j := f.2 r j 0 • conicVector (roots r) + f.2 r j 1 • conicVector (b j) -
    baseLiftCoefficient ω (roots r) (motionLinear (conicVector (b j)) (f.1 j))
  map_add' f g := by
    funext r j
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, map_add]
    abel
  map_smul' a f := by
    funext r j
    simp [smul_add, smul_sub, smul_smul, smul_eq_mul]

@[simp] theorem rootBlockMap_apply (ω : K) (roots b : Fin 3 → K) (f : RootBlockInput K)
    (r j : Fin 3) :
    rootBlockMap ω roots b f r j =
      f.2 r j 0 • conicVector (roots r) + f.2 r j 1 • conicVector (b j) -
        baseLiftCoefficient ω (roots r) (motionQuadratic (f.1 j) (conicVector (b j))) := rfl

private theorem cross_dot_endpoint_combination (r b a c : K) :
    (conicVector b ⨯₃ conicVector r) ⬝ᵥ (a • conicVector r + c • conicVector b) = 0 := by
  simp only [conic_chord_coefficients, smul_dotProduct, dotProduct_add, dotProduct_smul,
    chordNormal_dot_conic_left, chordNormal_dot_conic_right, smul_zero, add_zero]

/-- The chord projection removes both endpoint terms and detects the motion. -/
theorem rootBlockMap_projection (ω : K) (roots b : Fin 3 → K) (f : RootBlockInput K)
    (r j : Fin 3) :
    (conicVector (b j) ⨯₃ conicVector (roots r)) ⬝ᵥ rootBlockMap ω roots b f r j =
      -rootMotionProjection ω (b j) (roots r) (f.1 j) := by
  simp only [rootBlockMap_apply, dotProduct_sub, cross_dot_endpoint_combination, zero_sub,
    rootMotionProjection]

private theorem endpoint_combination_injective (r b : K) (hrb : r ≠ b) :
    Function.Injective (fun p : Fin 2 → K => p 0 • conicVector r + p 1 • conicVector b) := by
  intro p q h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  simp [conicVector] at h₀ h₁
  have hd : (b - r) * (p 1 - q 1) = 0 := by
    linear_combination h₁ - r * h₀
  have h₁' : p 1 = q 1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr hrb.symm))
  have h₀' : p 0 = q 0 := by linear_combination h₀ - h₁'
  funext i
  fin_cases i
  · exact h₀'
  · exact h₁'

/-- The three root probes first determine each motion, and the chord planes then
determine the two endpoint coefficients in each block. -/
theorem rootBlockMap_bijective [CharZero K] (ω : K) (roots b : Fin 3 → K)
    (hω : IsPrimitiveRoot ω 3) (hroots : ∀ r, roots r ≠ 0) (hinj : Function.Injective roots)
    (hq : ∀ r j, chordFactor (roots r) (b j) ≠ 0) :
    Function.Bijective (rootBlockMap ω roots b) := by
  have hne (r j : Fin 3) : roots r ≠ b j := by
    intro h
    exact hq r j (by simp [chordFactor, h])
  constructor
  · intro f g hfg
    have hu : f.1 = g.1 := by
      funext j
      apply (rootMotionProjection_bijective ω (b j) roots hω hroots hinj (fun r => hq r j)).1
      funext r
      have hp := congrArg (fun w : RootBlockOutput K =>
        (conicVector (b j) ⨯₃ conicVector (roots r)) ⬝ᵥ w r j) hfg
      change (conicVector (b j) ⨯₃ conicVector (roots r)) ⬝ᵥ rootBlockMap ω roots b f r j =
        (conicVector (b j) ⨯₃ conicVector (roots r)) ⬝ᵥ rootBlockMap ω roots b g r j at hp
      rw [rootBlockMap_projection, rootBlockMap_projection] at hp
      exact neg_injective hp
    apply Prod.ext hu
    funext r j
    apply endpoint_combination_injective (roots r) (b j) (hne r j)
    have hp := congrFun (congrFun hfg r) j
    rw [rootBlockMap_apply, rootBlockMap_apply, hu] at hp
    have hc := congrArg (fun v : Fin 3 → K => v +
      baseLiftCoefficient ω (roots r) (motionQuadratic (g.1 j) (conicVector (b j)))) hp
    simpa only [sub_add_cancel] using hc
  · intro w
    choose u hu using fun j : Fin 3 =>
      (rootMotionProjection_bijective ω (b j) roots hω hroots hinj (fun r => hq r j)).2
        (fun r => -((conicVector (b j) ⨯₃ conicVector (roots r)) ⬝ᵥ w r j))
    let y (r j : Fin 3) := w r j +
      baseLiftCoefficient ω (roots r) (motionQuadratic (u j) (conicVector (b j)))
    have hplane (r j : Fin 3) : chordNormal (b j) (roots r) ⬝ᵥ y r j = 0 := by
      have hp : (conicVector (b j) ⨯₃ conicVector (roots r)) ⬝ᵥ y r j = 0 := by
        dsimp only [y]
        rw [dotProduct_add]
        change ((conicVector (b j) ⨯₃ conicVector (roots r)) ⬝ᵥ w r j) +
          rootMotionProjection ω (b j) (roots r) (u j) = 0
        have hur : rootMotionProjection ω (b j) (roots r) (u j) =
            -((conicVector (b j) ⨯₃ conicVector (roots r)) ⬝ᵥ w r j) := congrFun (hu j) r
        rw [hur, add_neg_cancel]
      rw [conic_chord_coefficients, smul_dotProduct, smul_eq_mul] at hp
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (hne r j))
    have hex (r j : Fin 3) : ∃ a c : K, y r j = a • conicVector (roots r) + c • conicVector (b j) := by
      obtain ⟨c, a, he⟩ := exists_eq_smul_conicVector_add (b j) (roots r) (hne r j).symm
        (y r j) (hplane r j)
      exact ⟨a, c, he.trans (add_comm _ _)⟩
    choose a c hp using hex
    let p (r j : Fin 3) : Fin 2 → K := ![a r j, c r j]
    refine ⟨(u, p), ?_⟩
    funext r j
    rw [rootBlockMap_apply]
    change a r j • conicVector (roots r) + c r j • conicVector (b j) -
      baseLiftCoefficient ω (roots r) (motionQuadratic (u j) (conicVector (b j))) = w r j
    rw [← hp r j]
    exact add_sub_cancel_right _ _

/-- Change from motion and endpoint coefficients to the nine actual coefficient vectors. -/
def rootBlockEquiv [CharZero K] (ω : K) (roots b : Fin 3 → K)
    (hω : IsPrimitiveRoot ω 3) (hroots : ∀ r, roots r ≠ 0) (hinj : Function.Injective roots)
    (hq : ∀ r j, chordFactor (roots r) (b j) ≠ 0) :
    RootBlockInput K ≃ₗ[K] RootBlockOutput K :=
  LinearEquiv.ofBijective (rootBlockMap ω roots b)
    (rootBlockMap_bijective ω roots b hω hroots hinj hq)

@[simp] theorem rootBlockEquiv_apply [CharZero K] (ω : K) (roots b : Fin 3 → K)
    (hω : IsPrimitiveRoot ω 3) (hroots : ∀ r, roots r ≠ 0) (hinj : Function.Injective roots)
    (hq : ∀ r j, chordFactor (roots r) (b j) ≠ 0) (f : RootBlockInput K) (r j : Fin 3) :
    rootBlockEquiv ω roots b hω hroots hinj hq f r j =
      f.2 r j 0 • conicVector (roots r) + f.2 r j 1 • conicVector (b j) -
        baseLiftCoefficient ω (roots r) (motionQuadratic (f.1 j) (conicVector (b j))) := rfl

end IdealGeneration.TripleNormal
