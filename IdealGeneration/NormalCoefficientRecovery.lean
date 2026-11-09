module

public import IdealGeneration.NormalDegree

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Reconstruction and recovery of linear normal or trace coefficients. -/
noncomputable section
namespace IdealGeneration.NormalDegree
open MvPolynomial
variable (K : Type*) [Field K] (c m : ℕ)

/-- Every extended trace polynomial has normal degree zero. -/
theorem coneExtend_weighted (f : Poly K m) :
    (coneExtend K c m f).IsWeightedHomogeneous (normalWeight c m) 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using isWeightedHomogeneous_C (normalWeight c m) a
  | add f g hf hg => simpa using hf.add hg
  | mul_X f i hf =>
      simpa using hf.mul (isWeightedHomogeneous_X (R := K) (normalWeight c m) (i.natAdd c))

/-- Every extended normal polynomial has trace degree zero. -/
theorem pureExtend_weighted (f : Poly K c) :
    (pureExtend K c m f).IsWeightedHomogeneous (traceWeight c m) 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa [pureExtend] using isWeightedHomogeneous_C (traceWeight c m) a
  | add f g hf hg => simpa using hf.add hg
  | mul_X f i hf =>
      simpa using hf.mul (isWeightedHomogeneous_X (R := K) (traceWeight c m) (i.castAdd m))

/-- The pure-normal extension retains its normal degree. -/
theorem pureExtend_normal_homogeneous {d : ℕ} (f : Forms K c d) :
    (pureExtend K c m f.val).IsWeightedHomogeneous (normalWeight c m) d := by
  intro e he
  have hd := (pureExtendForm K c m d f).property he
  have ht := pureExtend_weighted K c m f.val he
  have hs := weight_add c m e
  have hd' : e.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
  omega

/-- Form a polynomial linear in the normal variables with trace coefficients. -/
def normalLinearProduct (d : ℕ) : (Fin c → Forms K m d) →ₗ[K] Forms K (c + m) (d + 1) :=
  (formMultiplication K (c + m) d).comp
    (show (Fin c → Forms K m d) →ₗ[K] (Fin (c + m) → Forms K (c + m) d) from
    { toFun := fun f => Fin.addCases (fun i => coneExtendForm K c m d (f i)) (fun _ : Fin m => 0)
      map_add' := by
        intro f g
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := by
        intro a f
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp })

/-- Form a polynomial linear in the trace variables with normal coefficients. -/
def traceLinearProduct (d : ℕ) : (Fin m → Forms K c d) →ₗ[K] Forms K (c + m) (d + 1) :=
  (formMultiplication K (c + m) d).comp
    (show (Fin m → Forms K c d) →ₗ[K] (Fin (c + m) → Forms K (c + m) d) from
    { toFun := fun f => Fin.addCases (fun _ : Fin c => 0) (fun i => pureExtendForm K c m d (f i))
      map_add' := by
        intro f g
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := by
        intro a f
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp })

@[simp] theorem normalLinearProduct_val {d : ℕ} (f : Fin c → Forms K m d) :
    (normalLinearProduct K c m d f).val =
      ∑ i : Fin c, X (i.castAdd m) * coneExtend K c m (f i).val := by
  simp [normalLinearProduct, formMultiplication, Fin.sum_univ_add, coneExtendForm]

@[simp] theorem traceLinearProduct_val {d : ℕ} (f : Fin m → Forms K c d) :
    (traceLinearProduct K c m d f).val =
      ∑ i : Fin m, X (i.natAdd c) * pureExtend K c m (f i).val := by
  simp [traceLinearProduct, formMultiplication, Fin.sum_univ_add, pureExtendForm]

/-- Derivation followed by restriction recovers each normal-linear coefficient. -/
@[simp] theorem linearCoefficientMap_product {d : ℕ} (f : Fin c → Forms K m d) :
    linearCoefficientMap K c m d (normalLinearProduct K c m d f) = f := by
  classical
  funext i
  apply Subtype.ext
  change coneRestrict K c m (pderiv (i.castAdd m) (normalLinearProduct K c m d f).val) = (f i).val
  rw [normalLinearProduct_val]
  simp [map_sum, pderiv_X, map_mul, Pi.single_apply, apply_ite]

/-- Derivation followed by restriction recovers each trace-linear coefficient. -/
@[simp] theorem traceCoefficientMap_product {d : ℕ} (f : Fin m → Forms K c d) :
    traceCoefficientMap K c m d (traceLinearProduct K c m d f) = f := by
  classical
  funext i
  apply Subtype.ext
  change pureRestrict K c m (pderiv (i.natAdd c) (traceLinearProduct K c m d f).val) = (f i).val
  rw [traceLinearProduct_val]
  simp [map_sum, pderiv_X, map_mul, Pi.single_apply, apply_ite]

theorem normalLinearProduct_injective (d : ℕ) : Function.Injective (normalLinearProduct K c m d) := by
  intro f g h
  have hh := congrArg (linearCoefficientMap K c m d) h
  simpa only [linearCoefficientMap_product] using hh

theorem traceLinearProduct_injective (d : ℕ) : Function.Injective (traceLinearProduct K c m d) := by
  intro f g h
  have hh := congrArg (traceCoefficientMap K c m d) h
  simpa only [traceCoefficientMap_product] using hh

theorem normalLinearProduct_weighted {d : ℕ} (f : Fin c → Forms K m d) :
    (normalLinearProduct K c m d f).val.IsWeightedHomogeneous (normalWeight c m) 1 := by
  rw [normalLinearProduct_val]
  apply IsWeightedHomogeneous.sum
  intro i _
  simpa using (isWeightedHomogeneous_X (R := K) (normalWeight c m) (i.castAdd m)).mul
    (coneExtend_weighted K c m (f i).val)

theorem traceLinearProduct_weighted {d : ℕ} (f : Fin m → Forms K c d) :
    (traceLinearProduct K c m d f).val.IsWeightedHomogeneous (normalWeight c m) d := by
  rw [traceLinearProduct_val]
  apply IsWeightedHomogeneous.sum
  intro i _
  simpa using (isWeightedHomogeneous_X (R := K) (normalWeight c m) (i.natAdd c)).mul
    (pureExtend_normal_homogeneous K c m (f i))

/-- A form with smaller normal degree vanishes on the pure-normal coordinate subspace. -/
theorem pureRestrict_eq_zero_of_lower_weight {d r : ℕ} (f : Forms K (c + m) d)
    (hf : f.val.IsWeightedHomogeneous (normalWeight c m) r) (hr : r < d) :
    pureRestrict K c m f.val = 0 := by
  apply weighted_positive_eval₂ K (traceWeight c m) f.val
    (trace_homogeneous K c m f.property hf (Nat.le_of_lt hr)) (by omega)
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hi; simp at hi
  · intro hi; simp

/-- Trace-linear coefficient extraction kills forms whose normal degree is too small. -/
theorem traceCoefficientMap_eq_zero_of_lower_weight {d r : ℕ}
    (f : Forms K (c + m) (d + 1))
    (hf : f.val.IsWeightedHomogeneous (normalWeight c m) r) (hr : r < d) :
    traceCoefficientMap K c m d f = 0 := by
  funext i
  apply Subtype.ext
  change pureRestrict K c m (pderiv (i.natAdd c) f.val) = 0
  have ht := trace_homogeneous K c m f.property hf (by omega)
  have hd : (pderiv (i.natAdd c) f.val).IsWeightedHomogeneous
      (traceWeight c m) (d - r) := ht.pderiv (by simp; omega)
  apply weighted_positive_eval₂ K (traceWeight c m) _ hd (by omega)
  intro j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · intro hj; simp at hj
  · intro hj; simp

/-- Reconstruction on the normal-weight-one subspace is the other inverse. -/
theorem normalLinearProduct_coefficient {d : ℕ} (f : Forms K (c + m) (d + 1))
    (hf : f.val.IsWeightedHomogeneous (normalWeight c m) 1) :
    normalLinearProduct K c m d (linearCoefficientMap K c m d f) = f := by
  apply Subtype.ext
  rw [normalLinearProduct_val]
  exact (linear_reconstruct K c m f hf).symm

end IdealGeneration.NormalDegree
