module

public import IdealGeneration.TripleNormalInitialData
public import IdealGeneration.ConeKernelMatrixBridge
public import IdealGeneration.ConeMiddleOpen
public import IdealGeneration.IntegerKernelChart
public import IdealGeneration.CyclotomicMatrixDescent
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Specialization of the checked three-normal initial coefficient matrices. -/
noncomputable section
namespace IdealGeneration.TripleNormalInitial
open MvPolynomial Matrix ConeMonomialChart IntegerKernelChart

private theorem modulus_prime : Nat.Prime 1009 := by norm_num

local instance : Fact (1 < 1009) := ⟨by decide⟩

abbrev Column := MiddleColumn 3 12 (Fin 14) (Fin 26)

def evalAt {R : Type*} [CommRing R] (ω : R) : Polynomial ℤ →+* R :=
  Polynomial.eval₂RingHom (Int.castRingHom R) ω

abbrev modEval := evalAt (374 : ZMod 1009)

def normalEvaluationPolynomial : Matrix (Fin 28) (Fin 28 ⊕ Fin 14) (Polynomial ℤ) :=
  evaluationMatrix pointPolynomial normalExponent

def traceEvaluationPolynomial : Matrix (Fin 52) (Fin 52 ⊕ Fin 26) (Polynomial ℤ) :=
  evaluationMatrix tracePolynomial traceExponent

def normalPivotPolynomial : Matrix (Fin 28) (Fin 28) (Polynomial ℤ) :=
  normalEvaluationPolynomial.submatrix id Sum.inl

def normalFreePolynomial : Matrix (Fin 28) (Fin 14) (Polynomial ℤ) :=
  normalEvaluationPolynomial.submatrix id Sum.inr

def tracePivotPolynomial : Matrix (Fin 52) (Fin 52) (Polynomial ℤ) :=
  traceEvaluationPolynomial.submatrix id Sum.inl

def traceFreePolynomial : Matrix (Fin 52) (Fin 26) (Polynomial ℤ) :=
  traceEvaluationPolynomial.submatrix id Sum.inr

/-- Specializing the symbolic normal evaluation matrix gives actual evaluation. -/
theorem normalEvaluationPolynomial_map {K : Type*} [Field K] (ω : K) :
    normalEvaluationPolynomial.map (evalAt ω) =
      evaluationMatrix (configuration ω).point normalExponent := by
  rw [normalEvaluationPolynomial, evaluationMatrix_map]
  congr 1
  funext i j
  exact (configuration_point_eq_eval ω i j).symm

/-- Specializing the symbolic trace evaluation matrix gives actual evaluation. -/
theorem traceEvaluationPolynomial_map {K : Type*} [Field K] (ω : K) :
    traceEvaluationPolynomial.map (evalAt ω) =
      evaluationMatrix (configuration ω).trace traceExponent := by
  rw [traceEvaluationPolynomial, evaluationMatrix_map]
  congr 1
  funext i j
  simp [evalAt, tracePolynomial, configuration]

/-- The selected pivot and free columns are the full normal evaluation matrix. -/
theorem normalEvaluation_split {K : Type*} [Field K] (ω : K) :
    evaluationMatrix (configuration ω).point normalExponent =
      Matrix.fromCols (normalPivotPolynomial.map (evalAt ω))
        (normalFreePolynomial.map (evalAt ω)) := by
  rw [← normalEvaluationPolynomial_map]
  ext i j
  cases j <;> rfl

/-- The selected pivot and free columns are the full trace evaluation matrix. -/
theorem traceEvaluation_split {K : Type*} [Field K] (ω : K) :
    evaluationMatrix (configuration ω).trace traceExponent =
      Matrix.fromCols (tracePivotPolynomial.map (evalAt ω))
        (traceFreePolynomial.map (evalAt ω)) := by
  rw [← traceEvaluationPolynomial_map]
  ext i j
  cases j <;> rfl

/-- Use the prescribed order on the 288 source columns. -/
def orderedMiddleMatrix {R : Type*} [CommSemiring R] (order : Column ≃ Fin 288)
    (Kn : Matrix (Fin 28 ⊕ Fin 14) (Fin 14) R)
    (Kt : Matrix (Fin 52 ⊕ Fin 26) (Fin 26) R) : Matrix (Fin 288) (Fin 288) R :=
  (middleMatrix normalExponent traceExponent cubicExponent Kn Kt).submatrix id order.symm

theorem orderedMiddleMatrix_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (order : Column ≃ Fin 288)
    (Kn : Matrix (Fin 28 ⊕ Fin 14) (Fin 14) R)
    (Kt : Matrix (Fin 52 ⊕ Fin 26) (Fin 26) R) :
    (orderedMiddleMatrix order Kn Kt).map f = orderedMiddleMatrix order (Kn.map f) (Kt.map f) := by
  change ((middleMatrix normalExponent traceExponent cubicExponent Kn Kt).map f).submatrix
    id order.symm = _
  rw [middleMatrix_map]
  rfl

def columnScale {R : Type*} (order : Column ≃ Fin 288) (a b : R) (j : Fin 288) : R :=
  Sum.elim (fun _ => a) (fun _ => b) (order.symm j)

/-- Clearing the two pivot denominators scales the corresponding column groups. -/
theorem orderedMiddleMatrix_scale {R : Type*} [CommSemiring R] (order : Column ≃ Fin 288)
    (Kn : Matrix (Fin 28 ⊕ Fin 14) (Fin 14) R)
    (Kt : Matrix (Fin 52 ⊕ Fin 26) (Fin 26) R) (a b : R) :
    orderedMiddleMatrix order (a • Kn) (b • Kt) =
      orderedMiddleMatrix order Kn Kt * Matrix.diagonal (columnScale order a b) := by
  ext i j
  rw [Matrix.mul_diagonal]
  cases h : order.symm j <;>
    simp [orderedMiddleMatrix, middleMatrix, columnScale, h, shiftedCoeff,
      smul_eq_mul, mul_add, Finset.mul_sum, mul_ite, mul_comm]

/-- Injectivity is independent of the chosen finite column order. -/
theorem middleMatrix_injective_of_ordered {K : Type*} [Field K] (order : Column ≃ Fin 288)
    (Kn : Matrix (Fin 28 ⊕ Fin 14) (Fin 14) K)
    (Kt : Matrix (Fin 52 ⊕ Fin 26) (Fin 26) K)
    (h : Function.Injective (orderedMiddleMatrix order Kn Kt).mulVec) :
    Function.Injective (middleMatrix normalExponent traceExponent cubicExponent Kn Kt).mulVec := by
  intro x y hxy
  have hh : orderedMiddleMatrix order Kn Kt *ᵥ (x ∘ order.symm) =
      orderedMiddleMatrix order Kn Kt *ᵥ (y ∘ order.symm) := by
    simpa [orderedMiddleMatrix, Matrix.submatrix_mulVec_equiv, Function.comp_def] using hxy
  have hx := h hh
  funext j
  simpa [Function.comp_def] using congrFun hx (order j)

/-- The finite certificates use the modular pivot inverses and the actual
selected coefficient determinant in the prescribed order. -/
structure ModularCertificate (order : Column ≃ Fin 288) where
  normalInverse : Matrix (Fin 28) (Fin 28) (ZMod 1009)
  traceInverse : Matrix (Fin 52) (Fin 52) (ZMod 1009)
  normal_inverse_mul : normalInverse * normalPivotPolynomial.map modEval = 1
  trace_inverse_mul : traceInverse * tracePivotPolynomial.map modEval = 1
  middle_det :
    (orderedMiddleMatrix order
      (normalizedKernelMatrix normalInverse (normalFreePolynomial.map modEval))
      (normalizedKernelMatrix traceInverse (traceFreePolynomial.map modEval))).det ≠ 0

/-- A certificate written in terms of checked kernel columns gives the same
normalized coordinate charts. -/
def modularCertificateOfKernelColumns (order : Column ≃ Fin 288)
    (Bn : Matrix (Fin 28) (Fin 28) (ZMod 1009)) (Bt : Matrix (Fin 52) (Fin 52) (ZMod 1009))
    (Kn : Matrix (Fin 28 ⊕ Fin 14) (Fin 14) (ZMod 1009))
    (Kt : Matrix (Fin 52 ⊕ Fin 26) (Fin 26) (ZMod 1009))
    (hn : Bn * normalPivotPolynomial.map modEval = 1)
    (ht : Bt * tracePivotPolynomial.map modEval = 1)
    (hnk : (normalEvaluationPolynomial.map modEval) * Kn = 0)
    (htk : (traceEvaluationPolynomial.map modEval) * Kt = 0)
    (hnf : Kn.submatrix Sum.inr id = 1) (htf : Kt.submatrix Sum.inr id = 1)
    (hm : (orderedMiddleMatrix order Kn Kt).det ≠ 0) : ModularCertificate order where
  normalInverse := Bn
  traceInverse := Bt
  normal_inverse_mul := hn
  trace_inverse_mul := ht
  middle_det := by
    have hns : Matrix.fromCols (normalPivotPolynomial.map modEval)
        (normalFreePolynomial.map modEval) = normalEvaluationPolynomial.map modEval := by
      ext i j
      cases j <;> rfl
    have hts : Matrix.fromCols (tracePivotPolynomial.map modEval)
        (traceFreePolynomial.map modEval) = traceEvaluationPolynomial.map modEval := by
      ext i j
      cases j <;> rfl
    rw [normalizedKernelMatrix_eq_of_verified _ Bn _ Kn hn (hns.symm ▸ hnk) hnf,
      normalizedKernelMatrix_eq_of_verified _ Bt _ Kt ht (hts.symm ▸ htk) htf]
    exact hm

/-- The normal and trace pivot minors specialize nontrivially at a primitive cube root. -/
theorem pivot_determinants {K : Type*} [Field K] [CharZero K] (ω : K)
    (hω : IsPrimitiveRoot ω 3) {order : Column ≃ Fin 288} (cert : ModularCertificate order) :
    (normalPivotPolynomial.map (evalAt ω)).det ≠ 0 ∧
      (tracePivotPolynomial.map (evalAt ω)).det ≠ 0 :=
  ⟨cubic_root_matrix_det_ne_zero normalPivotPolynomial ω hω
      (det_ne_zero_of_leftInverse _ cert.normalInverse cert.normal_inverse_mul),
    cubic_root_matrix_det_ne_zero tracePivotPolynomial ω hω
      (det_ne_zero_of_leftInverse _ cert.traceInverse cert.trace_inverse_mul)⟩

private theorem modular_mul_ne_zero {a b : ZMod 1009} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  let : Fact (Nat.Prime 1009) := ⟨modulus_prime⟩
  exact mul_ne_zero ha hb

set_option backward.isDefEq.respectTransparency false in
private theorem modular_det_ne_zero_of_scaled_columns {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι (ZMod 1009)) (v : ι → ZMod 1009)
    (hA : A.det ≠ 0) (hv : ∀ j, v j ≠ 0) (hB : ∀ i j, B i j = A i j * v j) :
    B.det ≠ 0 := by
  have hm : B = A * Matrix.diagonal v := by
    ext i j
    rw [Matrix.mul_diagonal]
    exact hB i j
  have hp (s : Finset ι) : (∏ j ∈ s, v j) ≠ 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj hs =>
      rw [Finset.prod_insert hj]
      exact modular_mul_ne_zero (hv j) hs
  rw [hm, Matrix.det_mul, Matrix.det_diagonal]
  exact modular_mul_ne_zero hA (hp Finset.univ)

private theorem cubic_root_matrix_injective_of_scaling {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] (ω : K)
    (hω : IsPrimitiveRoot ω 3) (A : Matrix ι ι (Polynomial ℤ))
    (B : Matrix ι ι (ZMod 1009)) (v : ι → ZMod 1009) (hB : B.det ≠ 0)
    (hv : ∀ j, v j ≠ 0) (hA : A.map modEval = B * Matrix.diagonal v) :
    Function.Injective (A.map (evalAt ω)).mulVec := by
  apply cubic_root_matrix_mulVec_injective A ω hω
  exact modular_det_ne_zero_of_scaled_columns B (A.map modEval) v hB hv (by
    intro i j
    rw [hA, Matrix.mul_diagonal])

private def clearedOrderedMiddle (order : Column ≃ Fin 288) :
    Matrix (Fin 288) (Fin 288) (Polynomial ℤ) :=
  orderedMiddleMatrix order
    (clearedKernelMatrix normalPivotPolynomial normalFreePolynomial)
    (clearedKernelMatrix tracePivotPolynomial traceFreePolynomial)

private def normalizedOrderedMiddle {order : Column ≃ Fin 288}
    (cert : ModularCertificate order) : Matrix (Fin 288) (Fin 288) (ZMod 1009) :=
  orderedMiddleMatrix order
    (normalizedKernelMatrix cert.normalInverse (normalFreePolynomial.map modEval))
    (normalizedKernelMatrix cert.traceInverse (traceFreePolynomial.map modEval))

private def orderedScales (order : Column ≃ Fin 288) : Fin 288 → ZMod 1009 :=
  columnScale order (normalPivotPolynomial.map modEval).det (tracePivotPolynomial.map modEval).det

private theorem columnScale_ne_zero (order : Column ≃ Fin 288) {a b : ZMod 1009}
    (ha : a ≠ 0) (hb : b ≠ 0) (j : Fin 288) : columnScale order a b j ≠ 0 := by
  unfold columnScale
  cases order.symm j
  · exact ha
  · exact hb

private theorem orderedScales_ne_zero {order : Column ≃ Fin 288}
    (cert : ModularCertificate order) (j : Fin 288) : orderedScales order j ≠ 0 :=
  columnScale_ne_zero order
    (det_ne_zero_of_leftInverse _ _ cert.normal_inverse_mul)
    (det_ne_zero_of_leftInverse _ _ cert.trace_inverse_mul) j

private theorem clearedOrderedMiddle_map_eq {order : Column ≃ Fin 288}
    (cert : ModularCertificate order) :
    (clearedOrderedMiddle order).map modEval =
      normalizedOrderedMiddle cert * Matrix.diagonal (orderedScales order) := by
  have hn := map_clearedKernelMatrix_eq_det_smul modEval normalPivotPolynomial normalFreePolynomial
    cert.normalInverse cert.normal_inverse_mul
  have ht := map_clearedKernelMatrix_eq_det_smul modEval tracePivotPolynomial traceFreePolynomial
    cert.traceInverse cert.trace_inverse_mul
  unfold clearedOrderedMiddle normalizedOrderedMiddle orderedScales
  rw [orderedMiddleMatrix_map, hn, ht]
  exact orderedMiddleMatrix_scale order _ _ _ _

/-- The selected modular witness gives the characteristic-zero matrix injection. -/
private theorem clearedMiddle_injective_at_root {K : Type*} [Field K] [CharZero K]
    (ω : K) (hω : IsPrimitiveRoot ω 3) {order : Column ≃ Fin 288}
    (cert : ModularCertificate order) :
    Function.Injective ((clearedOrderedMiddle order).map (evalAt ω)).mulVec := by
  exact cubic_root_matrix_injective_of_scaling ω hω (clearedOrderedMiddle order)
    (normalizedOrderedMiddle cert) (orderedScales order) cert.middle_det
    (orderedScales_ne_zero cert) (clearedOrderedMiddle_map_eq cert)

/-- The certified modular coefficient calculation yields injectivity of the
actual initial cone middle map in characteristic zero. -/
theorem middle_injective_of_certificate {K : Type*} [Field K] [CharZero K] (ω : K)
    (hω : IsPrimitiveRoot ω 3) {order : Column ≃ Fin 288} (cert : ModularCertificate order) :
    Function.Injective ((configuration ω).middleMultiplication 2) := by
  let Pn := normalPivotPolynomial.map (evalAt ω)
  let Qn := normalFreePolynomial.map (evalAt ω)
  let Pt := tracePivotPolynomial.map (evalAt ω)
  let Qt := traceFreePolynomial.map (evalAt ω)
  let Kn := clearedKernelMatrix Pn Qn
  let Kt := clearedKernelMatrix Pt Qt
  obtain ⟨hn, ht⟩ := pivot_determinants ω hω cert
  let Knp := clearedKernelMatrix normalPivotPolynomial normalFreePolynomial
  let Ktp := clearedKernelMatrix tracePivotPolynomial traceFreePolynomial
  have hchar := clearedMiddle_injective_at_root ω hω cert
  have hordered : Function.Injective (orderedMiddleMatrix order Kn Kt).mulVec := by
    unfold clearedOrderedMiddle at hchar
    change Function.Injective ((orderedMiddleMatrix order Knp Ktp).map (evalAt ω)).mulVec at hchar
    rw [orderedMiddleMatrix_map] at hchar
    dsimp only [Knp, Ktp] at hchar
    rw [clearedKernelMatrix_map, clearedKernelMatrix_map] at hchar
    exact hchar
  have hnormalSpan := normalSynth_surjective (K := K) (c := 3) (m := 12) (d := 2)
    (ι := Fin 28 ⊕ Fin 14) normalExponent normalExponent_degree
    normalExponent_support normalExponent_injective (by simp; decide)
  have htraceSpan := formSynth_surjective (K := K) (n := 12) (d := 2)
    (ι := Fin 52 ⊕ Fin 26) traceExponent traceExponent_degree traceExponent_injective (by simp; decide)
  apply middle_injective_of_kernel_chart_matrix (configuration ω) normalExponent traceExponent
    cubicExponent Kn Kt normalExponent_degree traceExponent_degree normalExponent_support
    hnormalSpan htraceSpan
  · intro u hu
    have hk : u ∈ (Matrix.fromCols Pn Qn).mulVecLin.ker := by
      change Matrix.fromCols Pn Qn *ᵥ u = 0
      rw [← normalEvaluation_split ω]
      exact hu
    rw [← clearedKernelMatrix_range_eq_ker Pn Qn hn] at hk
    exact hk
  · intro u hu
    have hk : u ∈ (Matrix.fromCols Pt Qt).mulVecLin.ker := by
      change Matrix.fromCols Pt Qt *ᵥ u = 0
      rw [← traceEvaluation_split ω]
      exact hu
    rw [← clearedKernelMatrix_range_eq_ker Pt Qt ht] at hk
    exact hk
  · exact middleMatrix_injective_of_ordered order Kn Kt hordered

private theorem fromCols_surjective_of_pivot {K ι κ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι ι K) (Q : Matrix ι κ K) (hP : P.det ≠ 0) :
    Function.Surjective (Matrix.fromCols P Q).mulVec := by
  intro y
  have hs : Function.Surjective P.mulVec :=
    LinearMap.surjective_of_injective (f := P.mulVecLin) (Matrix.mulVec_injective_of_det_ne_zero hP)
  obtain ⟨x, hx⟩ := hs y
  refine ⟨Sum.elim x (0 : κ → K), ?_⟩
  rw [Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, add_zero, hx]

/-- The certified normal pivot provides full scalar evaluation on the normal ideal. -/
theorem normalEvaluation_surjective_of_certificate {K : Type*} [Field K] [CharZero K]
    (ω : K) (hω : IsPrimitiveRoot ω 3) {order : Column ≃ Fin 288}
    (cert : ModularCertificate order) : Function.Surjective
      (ConeMiddleFamily.normalEvaluation support
        (ConeParameterSpace.encode (configuration ω)) 2) := by
  intro y
  have hdet := (pivot_determinants ω hω cert).1
  obtain ⟨u, hu⟩ := fromCols_surjective_of_pivot
    (normalPivotPolynomial.map (evalAt ω)) (normalFreePolynomial.map (evalAt ω)) hdet y
  refine ⟨normalSynth normalExponent normalExponent_degree normalExponent_support u, ?_⟩
  funext i
  change eval ((ConeParameterSpace.configuration support
      (ConeParameterSpace.encode (configuration ω))).point i) (synth normalExponent u) = y i
  rw [show support = (configuration ω).support from rfl,
    ConeParameterSpace.configuration_encode, evaluationMatrix_mulVec]
  change (evaluationMatrix (configuration ω).point normalExponent).mulVec u i = y i
  rw [normalEvaluation_split, hu]

/-- The certified trace pivot provides full scalar evaluation on the trace quadrics. -/
theorem traceEvaluation_surjective_of_certificate {K : Type*} [Field K] [CharZero K]
    (ω : K) (hω : IsPrimitiveRoot ω 3) {order : Column ≃ Fin 288}
    (cert : ModularCertificate order) : Function.Surjective
      (ConeParameterSpace.traceEvaluation (ConeParameterSpace.encode (configuration ω)) 2) := by
  intro y
  have hdet := (pivot_determinants ω hω cert).2
  obtain ⟨u, hu⟩ := fromCols_surjective_of_pivot
    (tracePivotPolynomial.map (evalAt ω)) (traceFreePolynomial.map (evalAt ω)) hdet y
  refine ⟨formSynth traceExponent traceExponent_degree u, ?_⟩
  funext i
  change eval ((configuration ω).trace i) (synth traceExponent u) = y i
  rw [evaluationMatrix_mulVec]
  change (evaluationMatrix (configuration ω).trace traceExponent).mulVec u i = y i
  rw [traceEvaluation_split, hu]

/-- Scalar postulation certifies that each cone representative is nonzero. -/
theorem point_ne_zero_of_certificate {K : Type*} [Field K] [CharZero K]
    (ω : K) (hω : IsPrimitiveRoot ω 3) {order : Column ≃ Fin 288}
    (cert : ModularCertificate order) (i : Fin 28) : (configuration ω).point i ≠ 0 := by
  intro hi
  obtain ⟨f, hf⟩ := normalEvaluation_surjective_of_certificate ω hω cert (fun _ => 1)
  have he := congrFun hf i
  change eval ((ConeParameterSpace.configuration support
      (ConeParameterSpace.encode (configuration ω))).point i) f.val.val = 1 at he
  rw [show support = (configuration ω).support from rfl,
    ConeParameterSpace.configuration_encode, hi] at he
  have hz : eval (0 : Fin 15 → K) f.val.val = 0 := by
    simpa using homogeneous_eval_scale f.val.property (0 : Fin 15 → K) (0 : K)
  exact zero_ne_one (hz.symm.trans he)

/-- The A.4 initial witness meets the scalar and middle-map conditions used
by the marked-cone specialization. -/
theorem fullEvaluation_of_certificate {K : Type*} [Field K] [CharZero K]
    (ω : K) (hω : IsPrimitiveRoot ω 3) {order : Column ≃ Fin 288}
    (cert : ModularCertificate order) : ConeMiddleFamily.FullEvaluation support
      (ConeParameterSpace.encode (configuration ω)) 2 := by
  apply ConeMiddleFamily.fullEvaluation_of_degree
  · rw [show support = (configuration ω).support from rfl,
      ConeParameterSpace.configuration_encode]
    exact point_ne_zero_of_certificate ω hω cert
  · exact normalEvaluation_surjective_of_certificate ω hω cert
  · exact traceEvaluation_surjective_of_certificate ω hω cert

end IdealGeneration.TripleNormalInitial
