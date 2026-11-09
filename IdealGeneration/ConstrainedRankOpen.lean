module

public import IdealGeneration.RankOpen
public import IdealGeneration.TwoGroupLinearCore

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Rank opens for maps between varying kernels

The ambient source and target remain fixed. Stacking the source constraints
with the ambient map expresses the rank of its restriction to the constraint
kernel. Constant ranks of the two constraint maps then turn ambient rank
persistence into surjectivity of the constrained map.
-/

noncomputable section
namespace IdealGeneration.ConstrainedRankOpen
open Module MvPolynomial
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {K V W C D : Type*} [Field K]
  [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
  [AddCommMonoid C] [Module K C] [AddCommMonoid D] [Module K D]


local instance (priority := 2000) submoduleCanonicalGroup
    {A : Type*} [AddCommMonoid A] [Module K A] (S : Submodule K A) : AddCommGroup S :=
  Module.addCommMonoidToAddCommGroup K

/-- The ambient map restricted to the source constraints and valued in the
kernel of the target constraints. -/
def constrainedMap (E : V →ₗ[K] C) (H : W →ₗ[K] D) (F : V →ₗ[K] W)
    (hpreserve : ∀ v, E v = 0 → H (F v) = 0) : E.ker →ₗ[K] H.ker where
  toFun v := ⟨F v.val, hpreserve v.val v.property⟩
  map_add' v w := Subtype.ext (F.map_add v.val w.val)
  map_smul' a v := Subtype.ext (F.map_smul a v.val)

@[simp] theorem constrainedMap_val (E : V →ₗ[K] C) (H : W →ₗ[K] D)
    (F : V →ₗ[K] W) (hpreserve : ∀ v, E v = 0 → H (F v) = 0) (v : E.ker) :
    (constrainedMap E H F hpreserve v).val = F v.val := rfl

/-- The constrained kernel is the kernel of the stacked ambient map. -/
def constrainedMap_kernelEquiv (E : V →ₗ[K] C) (H : W →ₗ[K] D)
    (F : V →ₗ[K] W) (hpreserve : ∀ v, E v = 0 → H (F v) = 0) :
    (constrainedMap E H F hpreserve).ker ≃ₗ[K] (E.prod F).ker where
  toFun v := ⟨v.val.val, by
    change (E v.val.val, F v.val.val) = (0, 0)
    exact Prod.ext v.val.property (congrArg Subtype.val v.property)⟩
  invFun v := ⟨⟨v.val, congrArg Prod.fst v.property⟩, by
    apply Subtype.ext
    exact congrArg Prod.snd v.property⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' a v := rfl

/-- Injectivity of the constrained map is ordinary injectivity of the stack. -/
theorem constrainedMap_injective_iff (E : V →ₗ[K] C) (H : W →ₗ[K] D)
    (F : V →ₗ[K] W) (hpreserve : ∀ v, E v = 0 → H (F v) = 0) :
    Function.Injective (constrainedMap E H F hpreserve) ↔ Function.Injective (E.prod F) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  constructor
  · intro hi v w heq
    have he : E v = E w := congrArg Prod.fst heq
    have hf : F v = F w := congrArg Prod.snd heq
    let z : E.ker := ⟨v - w, by change E (v - w) = 0; rw [map_sub, he, sub_self]⟩
    have hz : constrainedMap E H F hpreserve z = constrainedMap E H F hpreserve 0 := by
      apply Subtype.ext
      change F (v - w) = F 0
      rw [map_sub, hf, sub_self, map_zero]
    exact sub_eq_zero.mp (congrArg Subtype.val (hi hz))
  · intro hi v w heq
    apply Subtype.ext
    apply hi
    have hv : E v.val = 0 := v.property
    have hw : E w.val = 0 := w.property
    exact Prod.ext (hv.trans hw.symm) (congrArg Subtype.val heq)

section Dimensions
variable [Module.Finite K V]

/-- The restriction rank plus the source-constraint rank is the stack rank. -/
theorem constrainedMap_finrank_range_add (E : V →ₗ[K] C) (H : W →ₗ[K] D)
    (F : V →ₗ[K] W) (hpreserve : ∀ v, E v = 0 → H (F v) = 0) :
    finrank K (constrainedMap E H F hpreserve).range + finrank K E.range =
      finrank K (E.prod F).range := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  have hr := TwoGroup.rank_nullity_monoid (constrainedMap E H F hpreserve)
  have he := TwoGroup.rank_nullity_monoid E
  have hs := TwoGroup.rank_nullity_monoid (E.prod F)
  have hk := (constrainedMap_kernelEquiv E H F hpreserve).finrank_eq
  omega

/-- The constrained rank is the stack rank less the source-constraint rank. -/
theorem constrainedMap_finrank_range (E : V →ₗ[K] C) (H : W →ₗ[K] D)
    (F : V →ₗ[K] W) (hpreserve : ∀ v, E v = 0 → H (F v) = 0) :
    finrank K (constrainedMap E H F hpreserve).range =
      finrank K (E.prod F).range - finrank K E.range := by
  have h := constrainedMap_finrank_range_add E H F hpreserve
  omega

variable [Module.Finite K W]

/-- The constrained target dimension is its ambient dimension less the
rank of its defining constraints. -/
theorem constrainedMap_target_finrank (H : W →ₗ[K] D) :
    finrank K H.ker = finrank K W - finrank K H.range := by
  have h := TwoGroup.rank_nullity_monoid H
  omega

/-- A surjective constrained witness persists when stack rank does not
decrease and both constraint ranks remain fixed. -/
theorem constrainedMap_surjective_of_rank_bounds
    (E₀ E : V →ₗ[K] C) (H₀ H : W →ₗ[K] D) (F₀ F : V →ₗ[K] W)
    (hp₀ : ∀ v, E₀ v = 0 → H₀ (F₀ v) = 0)
    (hp : ∀ v, E v = 0 → H (F v) = 0)
    (hsurj : Function.Surjective (constrainedMap E₀ H₀ F₀ hp₀))
    (hstack : finrank K (E₀.prod F₀).range ≤ finrank K (E.prod F).range)
    (hE : finrank K E.range = finrank K E₀.range)
    (hH : finrank K H.range = finrank K H₀.range) :
    Function.Surjective (constrainedMap E H F hp) := by
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  have hr₀ := constrainedMap_finrank_range_add E₀ H₀ F₀ hp₀
  have hr := constrainedMap_finrank_range_add E H F hp
  have htarget : finrank K H.ker = finrank K H₀.ker := by
    rw [constrainedMap_target_finrank, constrainedMap_target_finrank, hH]
  have hwitness : finrank K (constrainedMap E₀ H₀ F₀ hp₀).range = finrank K H₀.ker := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have hupper := Submodule.finrank_le (constrainedMap E H F hp).range
  omega

end Dimensions

/-- The ordinary polynomial-family predicate for a map space, keeping the
caller's additive monoids as its underlying structures. -/
abbrev IsPolynomialMapFamily {ι : Type*} (A : (ι → K) → V →ₗ[K] W) : Prop :=
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  IsPolynomialFamily A

/-- A fixed ambient map is a polynomial map family. -/
theorem isPolynomialMapFamily_const {ι : Type*} (F : V →ₗ[K] W) :
    IsPolynomialMapFamily (fun _ : ι → K => F) := by
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  exact isPolynomialFamily_const F

section PolynomialFamilies
variable {ι : Type*} [Module.Finite K V]

/-- Polynomial source constraints and ambient maps have a polynomial stack. -/
theorem stack_isPolynomialFamily
    (E : (ι → K) → V →ₗ[K] C) (F : (ι → K) → V →ₗ[K] W)
    (hE : IsPolynomialMapFamily E) (hF : IsPolynomialMapFamily F) :
    IsPolynomialMapFamily (fun a => (E a).prod (F a)) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  have hE' : IsPolynomialFamily E := hE
  have hF' : IsPolynomialFamily F := hF
  change IsPolynomialFamily (fun a => (E a).prod (F a))
  apply isPolynomialFamily_linearMap
  intro v
  exact (hE'.linear_comp (LinearMap.applyₗ (R := K) (M₂ := C) v)).prod_mk
    (hF'.linear_comp (LinearMap.applyₗ (R := K) (M₂ := W) v))

variable [Module.Finite K W] [Module.Finite K C]

/-- A constrained injective witness gives a principal open of constrained
injections, even though the source and target kernels vary. -/
theorem constrainedMap_injective_principal_open
    (E : (ι → K) → V →ₗ[K] C) (H : (ι → K) → W →ₗ[K] D)
    (F : (ι → K) → V →ₗ[K] W)
    (hpreserve : ∀ a v, E a v = 0 → H a (F a v) = 0)
    (hE : IsPolynomialMapFamily E) (hF : IsPolynomialMapFamily F)
    (a₀ : ι → K)
    (hi : Function.Injective (constrainedMap (E a₀) (H a₀) (F a₀) (hpreserve a₀))) :
    ∃ P : MvPolynomial ι K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 →
        Function.Injective (constrainedMap (E a) (H a) (F a) (hpreserve a)) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  obtain ⟨P, hP, hgood⟩ := injective_polynomial_principal_open
    (fun a => (E a).prod (F a)) (stack_isPolynomialFamily E F hE hF) a₀
    ((constrainedMap_injective_iff (E a₀) (H a₀) (F a₀) (hpreserve a₀)).mp hi)
  exact ⟨P, hP, fun a ha =>
    (constrainedMap_injective_iff (E a) (H a) (F a) (hpreserve a)).mpr (hgood a ha)⟩

/-- A surjective constrained witness persists on a principal open inside
the locus where both constraint ranks equal their witness values. -/
theorem constrainedMap_surjective_principal_open_on_rank_locus
    (E : (ι → K) → V →ₗ[K] C) (H : (ι → K) → W →ₗ[K] D)
    (F : (ι → K) → V →ₗ[K] W)
    (hpreserve : ∀ a v, E a v = 0 → H a (F a v) = 0)
    (hE : IsPolynomialMapFamily E) (hF : IsPolynomialMapFamily F)
    (a₀ : ι → K)
    (hs : Function.Surjective (constrainedMap (E a₀) (H a₀) (F a₀) (hpreserve a₀))) :
    ∃ P : MvPolynomial ι K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 →
        finrank K (E a).range = finrank K (E a₀).range →
        finrank K (H a).range = finrank K (H a₀).range →
        Function.Surjective (constrainedMap (E a) (H a) (F a) (hpreserve a)) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  obtain ⟨P, hP, hgood⟩ := rank_polynomial_principal_open
    (fun a => (E a).prod (F a)) (stack_isPolynomialFamily E F hE hF) a₀
  refine ⟨P, hP, ?_⟩
  intro a ha he hh
  exact constrainedMap_surjective_of_rank_bounds (E a₀) (E a) (H a₀) (H a)
    (F a₀) (F a) (hpreserve a₀) (hpreserve a) hs (hgood a ha) he hh

variable [Module.Finite K D]

/-- At a witness where the two constraints already have their largest
ranks, intersecting their rank opens with the stack open gives an ordinary
principal open of surjective constrained maps. -/
theorem constrainedMap_surjective_principal_open_of_maximal_constraints
    (E : (ι → K) → V →ₗ[K] C) (H : (ι → K) → W →ₗ[K] D)
    (F : (ι → K) → V →ₗ[K] W)
    (hpreserve : ∀ a v, E a v = 0 → H a (F a v) = 0)
    (hE : IsPolynomialMapFamily E) (hH : IsPolynomialMapFamily H) (hF : IsPolynomialMapFamily F)
    (a₀ : ι → K)
    (hEmax : ∀ a, finrank K (E a).range ≤ finrank K (E a₀).range)
    (hHmax : ∀ a, finrank K (H a).range ≤ finrank K (H a₀).range)
    (hs : Function.Surjective (constrainedMap (E a₀) (H a₀) (F a₀) (hpreserve a₀))) :
    ∃ P : MvPolynomial ι K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 →
        Function.Surjective (constrainedMap (E a) (H a) (F a) (hpreserve a)) := by
  obtain ⟨P, hP, hgood⟩ := constrainedMap_surjective_principal_open_on_rank_locus
    E H F hpreserve hE hF a₀ hs
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup D := Module.addCommMonoidToAddCommGroup K
  obtain ⟨Q, hQ, hEQ⟩ := rank_polynomial_principal_open E hE a₀
  obtain ⟨R, hR, hHR⟩ := rank_polynomial_principal_open H hH a₀
  refine ⟨Q * R * P, ?_, ?_⟩
  · simpa only [map_mul] using mul_ne_zero (mul_ne_zero hQ hR) hP
  · intro a ha
    have hparts : eval a Q ≠ 0 ∧ eval a R ≠ 0 ∧ eval a P ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff, and_assoc] using ha
    exact hgood a hparts.2.2 (le_antisymm (hEmax a) (hEQ a hparts.1))
      (le_antisymm (hHmax a) (hHR a hparts.2.1))

/-- Surjectivity of both ambient constraint maps at the witness guarantees
that their ranks remain constant on suitable determinant opens. -/
theorem constrainedMap_surjective_principal_open
    (E : (ι → K) → V →ₗ[K] C) (H : (ι → K) → W →ₗ[K] D)
    (F : (ι → K) → V →ₗ[K] W)
    (hpreserve : ∀ a v, E a v = 0 → H a (F a v) = 0)
    (hE : IsPolynomialMapFamily E) (hH : IsPolynomialMapFamily H) (hF : IsPolynomialMapFamily F)
    (a₀ : ι → K) (hE₀ : Function.Surjective (E a₀)) (hH₀ : Function.Surjective (H a₀))
    (hs : Function.Surjective (constrainedMap (E a₀) (H a₀) (F a₀) (hpreserve a₀))) :
    ∃ P : MvPolynomial ι K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 →
        Function.Surjective (constrainedMap (E a) (H a) (F a) (hpreserve a)) := by
  apply constrainedMap_surjective_principal_open_of_maximal_constraints
    E H F hpreserve hE hH hF a₀ ?_ ?_ hs
  · intro a
    rw [LinearMap.range_eq_top.mpr hE₀, finrank_top]
    exact Submodule.finrank_le _
  · intro a
    rw [LinearMap.range_eq_top.mpr hH₀, finrank_top]
    exact Submodule.finrank_le _

end PolynomialFamilies
end IdealGeneration.ConstrainedRankOpen
