module

public import IdealGeneration.NormalDegree
public import IdealGeneration.TripleNormalDimension
public import IdealGeneration.TripleNormalKernel
public import IdealGeneration.TwoGroupLinearCore

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Three-normal cubic elimination

The maps use actual homogeneous polynomials. Pure normal quadrics are lifted
by a specified linear section, and the cubic correction subtracts those lifts
with their actual trace-coordinate coefficients.
-/

noncomputable section
namespace IdealGeneration.TripleNormal
open MvPolynomial NormalDegree

variable {K : Type*} [Field K] {m p q : ℕ}
  (C : ConeConfiguration K 3 m p q)

/-- The actual pure-normal quadratic restriction on the residual space. -/
def quadraticRestriction : C.residualPiece 2 →ₗ[K] Forms K 3 2 :=
  (pureRestrictForm K 3 m 2).comp (C.residualPiece 2).subtype

/-- Multiplication by the three normal coordinates. -/
def normalProduct : (Fin 3 → C.residualPiece 2) →ₗ[K] C.residualPiece 3 :=
  (C.residualMultiplication 2).comp
    (show (Fin 3 → C.residualPiece 2) →ₗ[K] (Fin (3 + m) → C.residualPiece 2) from
    { toFun := fun f => Fin.addCases f (fun _ : Fin m => 0)
      map_add' := by
        intro f g
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := by
        intro a f
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp })

/-- Multiplication by the trace coordinates. -/
def traceProduct : (Fin m → C.residualPiece 2) →ₗ[K] C.residualPiece 3 :=
  (C.residualMultiplication 2).comp
    (show (Fin m → C.residualPiece 2) →ₗ[K] (Fin (3 + m) → C.residualPiece 2) from
    { toFun := fun f => Fin.addCases (fun _ : Fin 3 => 0) f
      map_add' := by
        intro f g
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := by
        intro a f
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp })

@[simp] theorem normalProduct_val (f : Fin 3 → C.residualPiece 2) :
    (normalProduct C f).val.val = ∑ i : Fin 3, X (i.castAdd m) * (f i).val.val := by
  simp [normalProduct, ConeConfiguration.residualMultiplication, formMultiplication,
    Fin.sum_univ_add]

@[simp] theorem traceProduct_val (f : Fin m → C.residualPiece 2) :
    (traceProduct C f).val.val = ∑ i : Fin m, X (i.natAdd 3) * (f i).val.val := by
  simp [traceProduct, ConeConfiguration.residualMultiplication, formMultiplication,
    Fin.sum_univ_add]

/-- The triples whose pure normal cubic cancels. -/
abbrev Omega := tripleNormalOmega (K := K) (V := C.residualPiece 2) (quadraticRestriction C)

/-- The cubic formed by a compatible triple. -/
def omegaProduct : Omega C →ₗ[K] C.residualPiece 3 :=
  (normalProduct C).comp (Omega C).subtype

/-- Pure-normal restriction of normal-coordinate multiplication is the cubic
constraint in the dimension calculation. -/
theorem restrict_normalProduct (f : Fin 3 → C.residualPiece 2) :
    pureRestrictForm K 3 m 3 (normalProduct C f).val =
      tripleNormalConstraint (K := K) (V := C.residualPiece 2) (quadraticRestriction C) f := by
  apply Subtype.ext
  simp [pureRestrictForm, normalProduct_val, tripleNormalConstraint_apply,
    formMultiplication, quadraticRestriction]

/-- Every compatible normal product consists only of normal-degree-two terms. -/
theorem omegaProduct_weighted (eta : Omega C) :
    (omegaProduct C eta).val.val.IsWeightedHomogeneous (normalWeight 3 m) 2 := by
  have hsplit (i : Fin 3) := quadratic_split K 3 m (eta.val i).val (eta.val i).property.2
  have hpure : (∑ i : Fin 3, X (i.castAdd m) *
      pureExtend K 3 m (quadraticRestriction C (eta.val i)).val) = 0 := by
    have hh := congrArg (fun f : Forms K 3 3 => pureExtend K 3 m f.val) eta.property
    simpa [tripleNormalConstraint_apply, formMultiplication, map_sum, map_mul] using hh
  have hexpand : (omegaProduct C eta).val.val =
      ∑ i : Fin 3, X (i.castAdd m) * (componentForm K 3 m 1 (eta.val i).val).val := by
    change (normalProduct C eta.val).val.val = _
    rw [normalProduct_val]
    calc
      _ = ∑ i : Fin 3, X (i.castAdd m) *
          ((componentForm K 3 m 1 (eta.val i).val).val +
            pureExtend K 3 m (quadraticRestriction C (eta.val i)).val) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun f => X (i.castAdd m) * f) (hsplit i)
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib, hpure, add_zero]
  rw [hexpand]
  apply IsWeightedHomogeneous.sum
  intro i _
  simpa [componentForm] using (isWeightedHomogeneous_X (R := K) (normalWeight 3 m) (i.castAdd m)).mul
    (component_weighted K 3 m 1 (eta.val i).val.val)

/-- The trace-coordinate coefficient quadrics of the compatible cubic. -/
def coefficientQuadrics : Omega C →ₗ[K] (Fin m → Forms K 3 2) :=
  (traceCoefficientMap K 3 m 2).comp
    ((C.residualPiece 3).subtype.comp (omegaProduct C))

/-- The compatible cubic has the displayed trace-linear normal-quadratic expansion. -/
theorem coefficientQuadrics_reconstruct (eta : Omega C) :
    (omegaProduct C eta).val.val = ∑ b : Fin m, X (b.natAdd 3) *
      pureExtend K 3 m (coefficientQuadrics C eta b).val := by
  apply trace_linear_reconstruct K 3 m (omegaProduct C eta).val
  exact trace_homogeneous K 3 m (omegaProduct C eta).val.property
    (omegaProduct_weighted C eta) (by decide)

variable (L : Forms K 3 2 →ₗ[K] C.residualPiece 2)

/-- The sum of trace variables times chosen lifts of their quadratic coefficients. -/
def liftedCorrection : Omega C →ₗ[K] C.residualPiece 3 :=
  (traceProduct C).comp
    (LinearMap.pi (fun b => L.comp ((LinearMap.proj b).comp (coefficientQuadrics C))))

/-- Subtract the lifted normal-quadratic terms from the compatible cubic. -/
def eliminatedCubic : Omega C →ₗ[K] C.residualPiece 3 where
  toFun eta := omegaProduct C eta - liftedCorrection C L eta
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [map_add, Submodule.coe_sub, Submodule.coe_add]
    abel
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    simp
    rw [smul_sub]

@[simp] theorem eliminatedCubic_apply (eta : Omega C) :
    eliminatedCubic C L eta = omegaProduct C eta - liftedCorrection C L eta := rfl

/-- After subtraction, the cubic is the negative mixed part of the chosen lifts. -/
theorem eliminatedCubic_expansion
    (hL : ∀ Q, quadraticRestriction C (L Q) = Q) (eta : Omega C) :
    (eliminatedCubic C L eta).val.val =
      -∑ b : Fin m, X (b.natAdd 3) *
        (componentForm K 3 m 1 (L (coefficientQuadrics C eta b)).val).val := by
  have hsplit (b : Fin m) := quadratic_split K 3 m
    (L (coefficientQuadrics C eta b)).val (L (coefficientQuadrics C eta b)).property.2
  change (omegaProduct C eta).val.val -
    (traceProduct C (fun b => L (coefficientQuadrics C eta b))).val.val = _
  rw [coefficientQuadrics_reconstruct, traceProduct_val]
  have hs (b : Fin m) : (L (coefficientQuadrics C eta b)).val.val =
      (componentForm K 3 m 1 (L (coefficientQuadrics C eta b)).val).val +
        pureExtend K 3 m (coefficientQuadrics C eta b).val := by
    have hh := hsplit b
    change (L (coefficientQuadrics C eta b)).val.val =
      (componentForm K 3 m 1 (L (coefficientQuadrics C eta b)).val).val +
        pureExtend K 3 m (quadraticRestriction C (L (coefficientQuadrics C eta b))).val at hh
    rw [hL] at hh
    exact hh
  have hsum : (∑ b : Fin m, X (b.natAdd 3) * (L (coefficientQuadrics C eta b)).val.val) =
      ∑ b : Fin m, X (b.natAdd 3) *
        ((componentForm K 3 m 1 (L (coefficientQuadrics C eta b)).val).val +
          pureExtend K 3 m (coefficientQuadrics C eta b).val) := by
    apply Finset.sum_congr rfl
    intro b _
    exact congrArg (fun f => X (b.natAdd 3) * f) (hs b)
  rw [hsum]
  simp only [mul_add, Finset.sum_add_distrib]
  have cancel (a b : Poly K (3 + m)) : b - (a + b) = -a := by abel
  exact cancel _ _

/-- The chosen section makes the eliminated cubic homogeneous of normal degree one. -/
theorem eliminatedCubic_weighted
    (hL : ∀ Q, quadraticRestriction C (L Q) = Q) (eta : Omega C) :
    (eliminatedCubic C L eta).val.val.IsWeightedHomogeneous (normalWeight 3 m) 1 := by
  rw [eliminatedCubic_expansion C L hL eta]
  apply IsWeightedHomogeneous.neg
  apply IsWeightedHomogeneous.sum
  intro b _
  simpa [componentForm] using (isWeightedHomogeneous_X (R := K) (normalWeight 3 m) (b.natAdd 3)).mul
    (component_weighted K 3 m 1 (L (coefficientQuadrics C eta b)).val.val)

/-- The actual vector-valued trace quadric denoted by P_h in the paper. -/
def coefficientMap : Omega C →ₗ[K] (Fin 3 → Forms K m 2) :=
  (linearCoefficientMap K 3 m 2).comp
    ((C.residualPiece 3).subtype.comp (eliminatedCubic C L))

/-- Exact polynomial identity defining the three-normal coefficient map. -/
theorem elimination_identity (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (eta : Omega C) :
    (omegaProduct C eta).val.val -
      (∑ b : Fin m, X (b.natAdd 3) * (L (coefficientQuadrics C eta b)).val.val) =
      ∑ a : Fin 3, X (a.castAdd m) * coneExtend K 3 m (coefficientMap C L eta a).val := by
  have hh := linear_reconstruct K 3 m (eliminatedCubic C L eta).val
    (eliminatedCubic_weighted C L hL eta)
  change (eliminatedCubic C L eta).val.val =
    ∑ a : Fin 3, X (a.castAdd m) * coneExtend K 3 m (coefficientMap C L eta a).val at hh
  have hleft : (eliminatedCubic C L eta).val.val = (omegaProduct C eta).val.val -
      ∑ b : Fin m, X (b.natAdd 3) * (L (coefficientQuadrics C eta b)).val.val := by
    simp only [eliminatedCubic_apply, liftedCorrection, LinearMap.comp_apply,
      LinearMap.pi_apply, LinearMap.proj_apply, Submodule.coe_sub, traceProduct_val]
  rw [hleft] at hh
  exact hh

/-- The dimension of compatible triples is 3h+8 for any actual residual
quadratic space admitting the chosen section. -/
theorem finrank_Omega [CharZero K] (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (h : ℕ) (hker : Module.finrank K (quadraticRestriction C).ker = h) :
    Module.finrank K (Omega C) = 3 * h + 8 := by
  have hq : Function.Surjective (quadraticRestriction C) := fun Q => ⟨L Q, hL Q⟩
  have hquadrics : Module.finrank K (Forms K 3 2) = 6 := by rw [finrank_forms]; decide
  have hcubics : Module.finrank K (Forms K 3 3) = 10 := by rw [finrank_forms]; decide
  have hs := TwoGroup.rank_nullity_monoid (K := K)
    (U := C.residualPiece 2) (C := Forms K 3 2) (quadraticRestriction C)
  rw [LinearMap.range_eq_top.mpr hq, finrank_top, hquadrics, hker] at hs
  have honto := tripleNormalConstraint_surjective (K := K) (V := C.residualPiece 2)
    (quadraticRestriction C) hq
  have ht := TwoGroup.rank_nullity_monoid (K := K)
    (U := Fin 3 → C.residualPiece 2) (C := Forms K 3 3)
    (tripleNormalConstraint (K := K) (V := C.residualPiece 2) (quadraticRestriction C))
  rw [LinearMap.range_eq_top.mpr honto, finrank_top, hcubics] at ht
  let : Module.Free K (C.residualPiece 2) := Module.Free.of_divisionRing K (C.residualPiece 2)
  have hp : Module.finrank K (Fin 3 → C.residualPiece 2) =
      3 * Module.finrank K (C.residualPiece 2) := by
    rw [Module.finrank_pi_fintype (R := K) (M := fun _ : Fin 3 => C.residualPiece 2)]
    simp
  rw [hp] at ht
  change Module.finrank K (tripleNormalConstraint (K := K) (V := C.residualPiece 2)
    (quadraticRestriction C)).ker = 3 * h + 8
  omega

end IdealGeneration.TripleNormal
