module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The augmented multiplication problem has the kernel and cokernel of the remaining evaluation. -/

noncomputable section
namespace IdealGeneration.QuadraticAugmentedEvaluation

variable {K D M B C : Type*} [Field K]
  [AddCommMonoid D] [Module K D] [AddCommGroup M] [Module K M]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

/-- The coefficient vectors whose lifted values are already products. -/
def productCoefficients (f : D →ₗ[K] M) (g : B →ₗ[K] M) : Submodule K B :=
  f.range.comap g

/-- Evaluation on the coefficient vectors in the multiplication image. -/
def restrictedEvaluation (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C) :
    productCoefficients f g →ₗ[K] C :=
  e.comp (productCoefficients f g).subtype

/-- Adjoin coefficient vectors that vanish under the extra evaluation. -/
def augmented (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C) :
    D × e.ker →ₗ[K] M :=
  f.coprod (g.comp e.ker.subtype)

@[simp] theorem augmented_apply (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C)
    (d : D) (v : e.ker) : augmented f g e (d,v) = f d + g v.val := rfl

private theorem product_eq_neg (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C)
    (x : (augmented f g e).ker) : f x.val.1 = -g x.val.2.val := by
  have h : f x.val.1 + g x.val.2.val = 0 := LinearMap.mem_ker.mp x.property
  exact eq_neg_of_add_eq_zero_left h

/-- Recover the evaluation-kernel vector as the negative trace correction. -/
def kernelMap (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C) :
    (augmented f g e).ker →ₗ[K] (restrictedEvaluation f g e).ker where
  toFun x := ⟨⟨-x.val.2.val, by
    change g (-x.val.2.val) ∈ f.range
    rw [map_neg]
    exact ⟨x.val.1, product_eq_neg f g e x⟩⟩, by
    change e (-x.val.2.val) = 0
    rw [map_neg, LinearMap.mem_ker.mp x.val.2.property, neg_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    change -(x.val.2.val + y.val.2.val) = -x.val.2.val + -y.val.2.val
    exact neg_add _ _
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    change -(a • x.val.2.val) = a • -x.val.2.val
    exact (smul_neg _ _).symm

/-- An injective multiplication map gives a unique product preimage for
any coefficient vector in the restricted evaluation kernel. -/
def kernelEquiv (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C)
    (hf : Function.Injective f) :
    (augmented f g e).ker ≃ₗ[K] (restrictedEvaluation f g e).ker :=
  LinearEquiv.ofBijective (kernelMap f g e) (by
    constructor
    · intro x y h
      have hval : -x.val.2.val = -y.val.2.val :=
        congrArg (fun z : (restrictedEvaluation f g e).ker => z.val.val) h
      have hv : x.val.2 = y.val.2 := Subtype.ext (neg_inj.mp hval)
      apply Subtype.ext
      refine Prod.ext (hf ?_) hv
      rw [product_eq_neg f g e x, product_eq_neg f g e y, hv]
    · intro w
      have hw : g w.val.val ∈ f.range := w.val.property
      obtain ⟨d, hd⟩ := hw
      let v : e.ker := ⟨-w.val.val, by
        change e (-w.val.val) = 0
        have he : e w.val.val = 0 := LinearMap.mem_ker.mp w.property
        rw [map_neg, he, neg_zero]⟩
      refine ⟨⟨(d,v), ?_⟩, ?_⟩
      · change f d + g (-w.val.val) = 0
        rw [hd, map_neg, add_neg_cancel]
      · apply Subtype.ext
        apply Subtype.ext
        exact neg_neg _)

/-- Map a trace coefficient vector to its class in the augmented cokernel. -/
def augmentedClass (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C) :
    B →ₗ[K] (M ⧸ (augmented f g e).range) :=
  (augmented f g e).range.mkQ.comp g

/-- Map a trace coefficient vector to its class in the evaluation cokernel. -/
def evaluationClass (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C) :
    B →ₗ[K] (C ⧸ (restrictedEvaluation f g e).range) :=
  (restrictedEvaluation f g e).range.mkQ.comp e

/-- A lifted coefficient vanishes in the augmented cokernel exactly when it
is a sum of a product coefficient and an evaluation-kernel coefficient. -/
theorem augmentedClass_ker (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C) :
    (augmentedClass f g e).ker = productCoefficients f g ⊔ e.ker := by
  ext b
  change (Submodule.Quotient.mk (g b) : M ⧸ (augmented f g e).range) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨⟨d,v⟩, hv⟩
    have h : f d + g v.val = g b := hv
    refine Submodule.mem_sup.mpr ⟨b - v.val, ?_, v.val, v.property, sub_add_cancel _ _⟩
    change g (b - v.val) ∈ f.range
    refine ⟨d, ?_⟩
    rw [map_sub, ← h, add_sub_cancel_right]
  · intro hb
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
    have hu' : g u ∈ f.range := hu
    obtain ⟨d, hd⟩ := hu'
    refine ⟨(d, ⟨v,hv⟩), ?_⟩
    change f d + g v = g (u + v)
    rw [hd, map_add]

/-- The evaluation quotient has the same kernel on trace coefficients. -/
theorem evaluationClass_ker (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C) :
    (evaluationClass f g e).ker = productCoefficients f g ⊔ e.ker := by
  ext b
  change (Submodule.Quotient.mk (e b) : C ⧸ (restrictedEvaluation f g e).range) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨w, hw⟩
    have h : e w.val = e b := hw
    refine Submodule.mem_sup.mpr ⟨w.val, w.property, b - w.val, ?_, ?_⟩
    · change e (b - w.val) = 0
      rw [map_sub, h, sub_self]
    · rw [add_comm, sub_add_cancel]
  · intro hb
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
    refine ⟨⟨u, hu⟩, ?_⟩
    change e u = e (u + v)
    rw [map_add, LinearMap.mem_ker.mp hv, add_zero]

/-- If products and lifted coefficients span the target, every augmented
cokernel class comes from a trace coefficient vector. -/
theorem augmentedClass_surjective (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C)
    (hspan : f.range ⊔ g.range = ⊤) : Function.Surjective (augmentedClass f g e) := by
  intro z
  obtain ⟨m, rfl⟩ := (augmented f g e).range.mkQ_surjective z
  have hm : m ∈ f.range ⊔ g.range := by rw [hspan]; trivial
  obtain ⟨u, ⟨d, rfl⟩, v, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hm
  refine ⟨b, ?_⟩
  change (augmented f g e).range.mkQ (g b) =
    (augmented f g e).range.mkQ (f d + g b)
  have hzero : (augmented f g e).range.mkQ (f d) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero (augmented f g e).range).mpr
    exact ⟨(d,0), by simp [augmented_apply]⟩
  rw [map_add, hzero, zero_add]

/-- Surjective evaluation supplies all remaining evaluation classes. -/
theorem evaluationClass_surjective (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C)
    (he : Function.Surjective e) : Function.Surjective (evaluationClass f g e) :=
  (restrictedEvaluation f g e).range.mkQ_surjective.comp he

/-- The two cokernels identify the same quotient of the coefficient space. -/
def cokernelEquiv (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C)
    (hspan : f.range ⊔ g.range = ⊤) (he : Function.Surjective e) :
    (M ⧸ (augmented f g e).range) ≃ₗ[K] C ⧸ (restrictedEvaluation f g e).range :=
  ((augmentedClass f g e).quotKerEquivOfSurjective
    (augmentedClass_surjective f g e hspan)).symm.trans
    ((Submodule.quotEquivOfEq _ _ ((augmentedClass_ker f g e).trans
      (evaluationClass_ker f g e).symm)).trans
      ((evaluationClass f g e).quotKerEquivOfSurjective
        (evaluationClass_surjective f g e he)))

/-- A representative lifted from the coefficient space maps to its evaluation class. -/
@[simp] theorem cokernelEquiv_class (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C)
    (hspan : f.range ⊔ g.range = ⊤) (he : Function.Surjective e) (b : B) :
    cokernelEquiv f g e hspan he (augmentedClass f g e b) = evaluationClass f g e b := by
  simp [cokernelEquiv]

/-- Injectivity of the augmented map is exactly injectivity of the remaining evaluation. -/
theorem augmented_injective_iff (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C)
    (hf : Function.Injective f) :
    Function.Injective (augmented f g e) ↔ Function.Injective (restrictedEvaluation f g e) := by
  let : AddCommGroup D := Module.addCommMonoidToAddCommGroup K
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot,
    ← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (kernelEquiv f g e hf).toEquiv.subsingleton_congr

/-- Surjectivity of the augmented map is exactly surjectivity of the remaining evaluation. -/
theorem augmented_surjective_iff (f : D →ₗ[K] M) (g : B →ₗ[K] M) (e : B →ₗ[K] C)
    (hspan : f.range ⊔ g.range = ⊤) (he : Function.Surjective e) :
    Function.Surjective (augmented f g e) ↔ Function.Surjective (restrictedEvaluation f g e) := by
  rw [← LinearMap.range_eq_top, ← LinearMap.range_eq_top,
    ← Submodule.Quotient.subsingleton_iff, ← Submodule.Quotient.subsingleton_iff]
  exact (cokernelEquiv f g e hspan he).toEquiv.subsingleton_congr

end IdealGeneration.QuadraticAugmentedEvaluation
