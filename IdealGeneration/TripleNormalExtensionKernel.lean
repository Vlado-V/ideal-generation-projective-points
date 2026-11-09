module

public import IdealGeneration.TripleNormalExtensionMaps
public import IdealGeneration.TripleNormalKernelStages

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual square evaluation maps commute with restriction to the old flag. -/
noncomputable section
namespace IdealGeneration.TripleNormal

open MvPolynomial NormalDegree
set_option maxHeartbeats 600000

variable {K : Type*} [Field K] {h p q r : ℕ}

private theorem restriction_normalVariable (i : Fin 3) :
    extensionAmbientRestriction (K := K) h (X (i.castAdd (h + 3 + 4))) =
      X (i.castAdd (h + 4)) := by
  simpa [oldAmbientIndex] using
    extensionAmbientRestriction_X_old (K := K) (i.castAdd (h + 4))

private theorem restriction_traceVariable (i : Fin (h + 4)) :
    extensionAmbientRestriction (K := K) h (X ((oldTraceIndex h i).natAdd 3)) =
      X (i.natAdd 3) := by
  simpa [oldAmbientIndex] using
    extensionAmbientRestriction_X_old (K := K) (i.natAdd 3)

/-- Restriction of a trace-coordinate multiplication sum drops the new coordinates. -/
private theorem restriction_trace_sum
    (f : Fin (h + 3 + 4) → Poly K (3 + (h + 3 + 4))) :
    extensionAmbientRestriction h (∑ i, X (i.natAdd 3) * f i) =
      ∑ i : Fin (h + 4), X (i.natAdd 3) * extensionAmbientRestriction h (f (oldTraceIndex h i)) := by
  have hb (i : Fin h) :
      extensionAmbientRestriction (K := K) h (X (((i.castAdd 3).castAdd 4).natAdd 3)) =
        X ((i.castAdd 4).natAdd 3) := by
    simpa only [oldTraceIndex_base] using restriction_traceVariable (K := K) (i.castAdd 4)
  have hz (i : Fin 4) :
      extensionAmbientRestriction (K := K) h (X ((i.natAdd (h + 3)).natAdd 3)) =
        X ((i.natAdd h).natAdd 3) := by
    simpa only [oldTraceIndex_layer] using restriction_traceVariable (K := K) (i.natAdd h)
  simp only [Fin.sum_univ_add, map_add, map_sum, map_mul, hb, hz,
    extensionAmbientRestriction_X_new, zero_mul, Finset.sum_const_zero, add_zero,
    oldTraceIndex_base, oldTraceIndex_layer]

private theorem restriction_traceLinearProduct {d : ℕ}
    (f : Fin (h + 3 + 4) → Forms K 3 d) :
    extensionAmbientRestrictionForm h (d + 1) (traceLinearProduct K 3 (h + 3 + 4) d f) =
      traceLinearProduct K 3 (h + 4) d (fun i => f (oldTraceIndex h i)) := by
  apply Subtype.ext
  change extensionAmbientRestriction h (traceLinearProduct K 3 (h + 3 + 4) d f).val = _
  rw [traceLinearProduct_val, traceLinearProduct_val, restriction_trace_sum]
  simp only [extensionAmbientRestriction_pureExtend]

private theorem restriction_normalLinearProduct {d : ℕ}
    (f : Fin 3 → Forms K (h + 3 + 4) d) :
    extensionAmbientRestrictionForm h (d + 1) (normalLinearProduct K 3 (h + 3 + 4) d f) =
      normalLinearProduct K 3 (h + 4) d (fun i => extensionTraceRestrictionForm h d (f i)) := by
  apply Subtype.ext
  change extensionAmbientRestriction h (normalLinearProduct K 3 (h + 3 + 4) d f).val = _
  rw [normalLinearProduct_val, normalLinearProduct_val, map_sum]
  simp only [map_mul, restriction_normalVariable, extensionAmbientRestriction_coneExtend]
  rfl

variable (C : ConeConfiguration K 3 (h + 4) p q) (a : Fin r × Fin (h + 3) → K)
  (ζ : Fin 4 → K) (n : Fin 3 → Fin 2 → Fin 3 → K)

local notation "Cnew" => supportedExtension C a ζ n
local notation "R₂" => supportedExtensionResidualRestriction C a ζ n 2
local notation "R₃" => supportedExtensionResidualRestriction C a ζ n 3

private theorem restriction_omegaProduct (x : Omega Cnew) :
    R₃ (omegaProduct Cnew x) = omegaProduct C (supportedExtensionOmegaRestriction C a ζ n x) := by
  apply Subtype.ext
  apply Subtype.ext
  change extensionAmbientRestriction h (normalProduct Cnew x.val).val.val =
    (normalProduct C (fun i => R₂ (x.val i))).val.val
  rw [normalProduct_val, normalProduct_val, map_sum]
  simp only [map_mul, restriction_normalVariable]
  rfl

private theorem omegaProduct_eq_traceLinear {m p' q' : ℕ}
    (D : ConeConfiguration K 3 m p' q') (x : Omega D) :
    (omegaProduct D x).val = traceLinearProduct K 3 m 2 (coefficientQuadrics D x) := by
  apply Subtype.ext
  rw [traceLinearProduct_val, coefficientQuadrics_reconstruct]

/-- Coefficients of surviving trace variables are unchanged by restriction. -/
theorem supportedExtension_coefficientQuadrics (x : Omega Cnew) :
    coefficientQuadrics C (supportedExtensionOmegaRestriction C a ζ n x) =
      fun i => coefficientQuadrics Cnew x (oldTraceIndex h i) := by
  let x₀ := supportedExtensionOmegaRestriction C a ζ n x
  let u : Fin (h + 4) → Forms K 3 2 := coefficientQuadrics C x₀
  let f : Fin (h + 3 + 4) → Forms K 3 2 := coefficientQuadrics Cnew x
  let g : Fin (h + 4) → Forms K 3 2 := fun i => f (oldTraceIndex h i)
  let T := traceLinearProduct K 3 (h + 4) 2
  let T' := traceLinearProduct K 3 (h + 3 + 4) 2
  let R := extensionAmbientRestrictionForm (K := K) h 3
  have hold : T u = (omegaProduct C x₀).val :=
    (omegaProduct_eq_traceLinear C x₀).symm
  have hprod : R (omegaProduct Cnew x).val = (omegaProduct C x₀).val :=
    congrArg (fun z : C.residualPiece 3 => z.val) (restriction_omegaProduct C a ζ n x)
  have hnew : (omegaProduct Cnew x).val = T' f := omegaProduct_eq_traceLinear Cnew x
  have hR : R (T' f) = T g :=
    restriction_traceLinearProduct (K := K) (h := h) (d := 2) f
  have hrestrict : R (omegaProduct Cnew x).val = R (T' f) :=
    congrArg (fun z : Forms K (3 + (h + 3 + 4)) 3 => R z) hnew
  have hfirst : T u = R (omegaProduct Cnew x).val :=
    hold.trans hprod.symm
  have hlast : R (omegaProduct Cnew x).val = T g := hrestrict.trans hR
  have hresult : T u = T g := hfirst.trans hlast
  have hinj : Function.Injective T := traceLinearProduct_injective K 3 (h + 4) 2
  change u = g
  exact @hinj u g hresult

variable (L : Forms K 3 2 →ₗ[K] C.residualPiece 2)
  (Lnew : Forms K 3 2 →ₗ[K] (supportedExtension C a ζ n).residualPiece 2)
  (hcompat : ∀ Q, supportedExtensionResidualRestriction C a ζ n 2 (Lnew Q) = L Q)

include hcompat in
private theorem restriction_liftedCorrection (x : Omega Cnew) :
    R₃ (liftedCorrection Cnew Lnew x) =
      liftedCorrection C L (supportedExtensionOmegaRestriction C a ζ n x) := by
  apply Subtype.ext
  apply Subtype.ext
  change extensionAmbientRestriction h
      (traceProduct Cnew (fun i => Lnew (coefficientQuadrics Cnew x i))).val.val =
    (traceProduct C (fun i => L (coefficientQuadrics C
      (supportedExtensionOmegaRestriction C a ζ n x) i))).val.val
  rw [traceProduct_val, traceProduct_val, restriction_trace_sum,
    supportedExtension_coefficientQuadrics]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f : C.residualPiece 2 => X (i.natAdd 3) * f.val.val)
    (hcompat (coefficientQuadrics Cnew x (oldTraceIndex h i)))

private theorem restriction_mixedProduct (x : Fin (h + 3 + 4) → MixedKernel Cnew) :
    R₃ (mixedProduct Cnew x) = mixedProduct C
      (fun i => supportedExtensionMixedRestriction C a ζ n (x (oldTraceIndex h i))) := by
  apply Subtype.ext
  apply Subtype.ext
  change extensionAmbientRestriction h (mixedProduct Cnew x).val.val = _
  rw [mixedProduct_val, mixedProduct_val, restriction_trace_sum]
  rfl

include hcompat

private theorem restriction_reducedPolynomial (x : EvaluationSource Cnew) :
    R₃ (reducedPolynomial Cnew Lnew x) =
      reducedPolynomial C L (supportedExtensionEvaluationSourceRestriction C a ζ n x) := by
  apply Subtype.ext
  apply Subtype.ext
  change extensionAmbientRestriction h ((omegaProduct Cnew x.1).val.val -
    (liftedCorrection Cnew Lnew x.1).val.val + (mixedProduct Cnew x.2).val.val) =
    (omegaProduct C (supportedExtensionOmegaRestriction C a ζ n x.1)).val.val -
      (liftedCorrection C L (supportedExtensionOmegaRestriction C a ζ n x.1)).val.val +
      (mixedProduct C (fun i =>
        supportedExtensionMixedRestriction C a ζ n (x.2 (oldTraceIndex h i)))).val.val
  have hω : extensionAmbientRestriction h (omegaProduct Cnew x.1).val.val =
      (omegaProduct C (supportedExtensionOmegaRestriction C a ζ n x.1)).val.val :=
    congrArg (fun f : C.residualPiece 3 => f.val.val) (restriction_omegaProduct C a ζ n x.1)
  have hcorr : extensionAmbientRestriction h (liftedCorrection Cnew Lnew x.1).val.val =
      (liftedCorrection C L (supportedExtensionOmegaRestriction C a ζ n x.1)).val.val :=
    congrArg (fun f : C.residualPiece 3 => f.val.val)
      (restriction_liftedCorrection C a ζ n L Lnew hcompat x.1)
  have hmix : extensionAmbientRestriction h (mixedProduct Cnew x.2).val.val =
      (mixedProduct C (fun i =>
        supportedExtensionMixedRestriction C a ζ n (x.2 (oldTraceIndex h i)))).val.val :=
    congrArg (fun f : C.residualPiece 3 => f.val.val) (restriction_mixedProduct C a ζ n x.2)
  rw [map_add, map_sub, hω, hcorr, hmix]

private theorem restriction_reducedCoefficient
    (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (hLnew : ∀ Q, quadraticRestriction Cnew (Lnew Q) = Q) (x : EvaluationSource Cnew) :
    (fun i => extensionTraceRestrictionForm h 2 (reducedCoefficient Cnew Lnew x i)) =
      reducedCoefficient C L (supportedExtensionEvaluationSourceRestriction C a ζ n x) := by
  let x₀ := supportedExtensionEvaluationSourceRestriction C a ζ n x
  let cnew := reducedCoefficient Cnew Lnew x
  let cold := reducedCoefficient C L x₀
  have hpoly : extensionAmbientRestrictionForm h 3 (reducedPolynomial Cnew Lnew x).val =
      (reducedPolynomial C L x₀).val :=
    congrArg (fun f : C.residualPiece 3 => f.val)
      (restriction_reducedPolynomial C a ζ n L Lnew hcompat x)
  apply normalLinearProduct_injective K 3 (h + 4) 2
  calc
    normalLinearProduct K 3 (h + 4) 2 (fun i => extensionTraceRestrictionForm h 2 (cnew i)) =
        extensionAmbientRestrictionForm h 3 (normalLinearProduct K 3 (h + 3 + 4) 2 cnew) :=
      (restriction_normalLinearProduct cnew).symm
    _ = extensionAmbientRestrictionForm h 3 (reducedPolynomial Cnew Lnew x).val :=
      congrArg (fun f : Forms K (3 + (h + 3 + 4)) 3 => extensionAmbientRestrictionForm h 3 f)
        (reduced_reconstruct Cnew Lnew hLnew x)
    _ = (reducedPolynomial C L x₀).val := hpoly
    _ = normalLinearProduct K 3 (h + 4) 2 cold := (reduced_reconstruct C L hL x₀).symm

/-- The actual geometrically allowed evaluation square commutes with forgetting
the three new base variables and the associated new trace rows. -/
theorem supportedExtension_allowedEvaluation_commutes
    (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (hLnew : ∀ Q, quadraticRestriction Cnew (Lnew Q) = Q)
    (hh : ∀ i, C.height i ≠ 0) (hhnew : ∀ i, (Cnew).height i ≠ 0)
    (x : EvaluationSource Cnew) :
    supportedExtensionAllowedRestriction C a ζ n (allowedEvaluationMap Cnew Lnew hLnew hhnew x) =
      allowedEvaluationMap C L hL hh (supportedExtensionEvaluationSourceRestriction C a ζ n x) := by
  apply Subtype.ext
  funext i j
  let f : Forms K (h + 3 + 4) 2 := reducedCoefficient Cnew Lnew x i
  let g : Forms K (h + 4) 2 :=
    reducedCoefficient C L (supportedExtensionEvaluationSourceRestriction C a ζ n x) i
  let f₀ : Forms K (h + 4) 2 := extensionTraceRestrictionForm h 2 f
  change eval ((Cnew).trace (j.castAdd (3 + (r + 4)))) f.val = eval (C.trace j) g.val
  have hcoeff : f₀ = g :=
    congrFun (restriction_reducedCoefficient C a ζ n L Lnew hcompat hL hLnew x) i
  calc
    eval ((Cnew).trace (j.castAdd (3 + (r + 4)))) f.val = eval (embedOldTrace (C.trace j)) f.val :=
      congrArg (fun z : Fin (h + 3 + 4) → K => eval z f.val)
        (supportedExtension_trace_old C a ζ n j)
    _ = eval (C.trace j) f₀.val := by
      change _ = eval (C.trace j) (extensionTraceRestriction h f.val)
      exact (eval_extensionTraceRestriction (C.trace j) f.val).symm
    _ = eval (C.trace j) g.val :=
      congrArg (fun F : Forms K (h + 4) 2 => eval (C.trace j) F.val) hcoeff

/-- Once the old square is injective, testing the enlarged square reduces
to vectors whose old source coordinates vanish. -/
theorem supportedExtension_allowedEvaluation_injective
    (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (hLnew : ∀ Q, quadraticRestriction Cnew (Lnew Q) = Q)
    (hh : ∀ i, C.height i ≠ 0) (hhnew : ∀ i, (Cnew).height i ≠ 0)
    (hold : Function.Injective (allowedEvaluationMap C L hL hh))
    (hnew : ∀ x : EvaluationSource Cnew,
      supportedExtensionEvaluationSourceRestriction C a ζ n x = 0 →
      allowedEvaluationMap Cnew Lnew hLnew hhnew x = 0 → x = 0) :
    Function.Injective (allowedEvaluationMap Cnew Lnew hLnew hhnew) := by
  apply (linearMap_injective_iff_kernel_subsingleton (allowedEvaluationMap Cnew Lnew hLnew hhnew)).mpr
  have hzero (x : (allowedEvaluationMap Cnew Lnew hLnew hhnew).ker) : x.val = 0 := by
    have hx := LinearMap.mem_ker.mp x.property
    have hleft : allowedEvaluationMap C L hL hh
        (supportedExtensionEvaluationSourceRestriction C a ζ n x.val) =
        allowedEvaluationMap C L hL hh 0 := by
      calc
        _ = supportedExtensionAllowedRestriction C a ζ n (allowedEvaluationMap Cnew Lnew hLnew hhnew x.val) :=
          (supportedExtension_allowedEvaluation_commutes C a ζ n L Lnew hcompat hL hLnew hh hhnew x.val).symm
        _ = supportedExtensionAllowedRestriction C a ζ n 0 :=
          congrArg (supportedExtensionAllowedRestriction C a ζ n) hx
        _ = 0 := (supportedExtensionAllowedRestriction C a ζ n).map_zero
        _ = _ := (allowedEvaluationMap C L hL hh).map_zero.symm
    exact hnew x.val (hold hleft) hx
  exact ⟨fun x y => Subtype.ext ((hzero x).trans (hzero y).symm)⟩

end IdealGeneration.TripleNormal
