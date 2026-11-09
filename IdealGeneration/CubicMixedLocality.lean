module

public import IdealGeneration.CubicLiftDecomposition

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Locality of the linear corrections in the supported cubic graph lift. -/

namespace IdealGeneration.CubicMixedLocality

open CubicSupported

/-- An increasing coordinate embedding sends an edge to its increasing image. -/
def edgeImage {n m : ℕ} (ι : Fin n ↪ Fin m) (hι : StrictMono ι) (e : Edge n) : Edge m :=
  ⟨(ι e.val.1, ι e.val.2), hι e.property⟩

@[simp] theorem edgeImage_fst {n m : ℕ} (ι : Fin n ↪ Fin m) (hι : StrictMono ι) (e : Edge n) :
    (edgeImage ι hι e).val.1 = ι e.val.1 := rfl

@[simp] theorem edgeImage_snd {n m : ℕ} (ι : Fin n ↪ Fin m) (hι : StrictMono ι) (e : Edge n) :
    (edgeImage ι hι e).val.2 = ι e.val.2 := rfl

variable {K : Type*} [Field K] {n m : ℕ}

/-- Agreement of the primitive parameters used by the mixed lift at `c`. -/
structure AgreesAt (P : Parameters K n) (L : Parameters K m)
    (ι : Fin n ↪ Fin m) (hι : StrictMono ι) (c : Fin n) : Prop where
  vertexSlope_eq : P.vertexSlope c = L.vertexSlope (ι c)
  vertexHeight_eq : P.vertexHeight c = L.vertexHeight (ι c)
  edge_eq : ∀ e : Edge n, e.val.1 = c ∨ e.val.2 = c →
    P.single e = L.single (edgeImage ι hι e) ∧
    P.edgeLambda e = L.edgeLambda (edgeImage ι hι e) ∧
    P.edgeSlope e = L.edgeSlope (edgeImage ι hι e) ∧
    P.edgeHeight e = L.edgeHeight (edgeImage ι hι e)

private theorem diagonalLift_zero_at {v : ℕ} (P : Parameters K v)
    (B : Fin v → Fin 3 → K) (i : Fin v) (h : B i = 0) : P.diagonalLift 0 B i = 0 := by
  funext k
  fin_cases k <;>
    simp [Parameters.diagonalLift, Parameters.diagonalRhs, solveTwo, normalCubic, normalQuadratic, h]

/-- The mixed lift depends on the center's vertex parameters and its incident edges.
The diagonal solve at every other vertex is zero. -/
theorem mixedLinear_eq_of_agreesAt
    {P : Parameters K n} {L : Parameters K m} {ι : Fin n ↪ Fin m}
    {hι : StrictMono ι} {c : Fin n} (h : AgreesAt P L ι hι c)
    (Q : Fin 3 → K) (j : Fin n) : P.mixedLinear c Q j = L.mixedLinear (ι c) Q (ι j) := by
  have hB (i : Fin n) :
      Parameters.mixedArray c Q i = Parameters.mixedArray (ι c) Q (ι i) := by
    by_cases hi : i = c
    · subst i
      simp [Parameters.mixedArray]
    · have hi' : ι i ≠ ι c := fun he => hi (ι.injective he)
      simp [Parameters.mixedArray, hi, hi']
  have hD (i : Fin n) :
      P.diagonalLift 0 (Parameters.mixedArray c Q) i =
        L.diagonalLift 0 (Parameters.mixedArray (ι c) Q) (ι i) := by
    by_cases hi : i = c
    · subst i
      simp [Parameters.diagonalLift, Parameters.diagonalRhs, Parameters.mixedArray,
        h.vertexSlope_eq, h.vertexHeight_eq]
    · have hz : Parameters.mixedArray c Q i = 0 := by simp [Parameters.mixedArray, hi]
      exact (diagonalLift_zero_at P _ i hz).trans
        (diagonalLift_zero_at L _ (ι i) ((hB i).symm.trans hz)).symm
  have hE (e : Edge n) (he : e.val.1 = c ∨ e.val.2 = c) :
      P.offDiagonalLift 0 (Parameters.mixedArray c Q) 0 e =
        L.offDiagonalLift 0 (Parameters.mixedArray (ι c) Q) 0 (edgeImage ι hι e) := by
    obtain ⟨hsingle, hlam, hslope, hheight⟩ := h.edge_eq e he
    have hRhs (d : Fin 2) :
        P.edgeRhs 0 (Parameters.mixedArray c Q) e d =
          L.edgeRhs 0 (Parameters.mixedArray (ι c) Q) (edgeImage ι hι e) d := by
      simp only [Parameters.edgeRhs, edgeImage_fst, edgeImage_snd,
        hlam, hslope, hheight, hB, hD]
    by_cases hs : P.single e = true
    · have hs' : L.single (edgeImage ι hι e) = true := hsingle.symm.trans hs
      simp [Parameters.offDiagonalLift, hs, hs', hRhs]
    · have hs' : ¬ L.single (edgeImage ι hι e) = true := fun he' => hs (hsingle.trans he')
      simp [Parameters.offDiagonalLift, hs, hs', hslope, hRhs]
  by_cases hcj : c < j
  · simp only [Parameters.mixedLinear, dite_eq_left hcj, dite_eq_left (hι hcj)]
    exact hE ⟨(c, j), hcj⟩ (Or.inl rfl)
  · by_cases hjc : j < c
    · have hcj' : ¬ ι c < ι j := not_lt_of_ge (hι hjc).le
      simp only [Parameters.mixedLinear, dite_eq_right hcj, dite_eq_left hjc,
        dite_eq_right hcj', dite_eq_left (hι hjc)]
      exact hE ⟨(j, c), hjc⟩ (Or.inr rfl)
    · have heq : j = c := le_antisymm (le_of_not_gt hcj) (le_of_not_gt hjc)
      subst j
      simp [Parameters.mixedLinear]
      exact hD c

/-- At fixed endpoints, a mixed correction is linear in the normal quadratic. -/
noncomputable def mixedLinearMap (P : Parameters K m) (c j : Fin m) :
    (Fin 3 → K) →ₗ[K] (Fin 2 → K) where
  toFun Q := P.mixedLinear c Q j
  map_add' Q Q' := by
    have h : P.mixedCubic c (Q + Q') = P.mixedCubic c Q + P.mixedCubic c Q' := by
      apply P.kernelCoordinatesEquiv.injective
      simp only [Parameters.mixedCubic, map_add, P.kernelCoordinatesEquiv_coefficientLift]
      refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
      funext i q
      by_cases hi : i = c <;> simp [Parameters.mixedArray, hi]
    simp only [Parameters.mixedLinear, h]
    split_ifs <;> rfl
  map_smul' r Q := by
    have h : P.mixedCubic c (r • Q) = r • P.mixedCubic c Q := by
      apply P.kernelCoordinatesEquiv.injective
      simp only [Parameters.mixedCubic, map_smul, P.kernelCoordinatesEquiv_coefficientLift]
      refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
      funext i q
      by_cases hi : i = c <;> simp [Parameters.mixedArray, hi]
    simp only [Parameters.mixedLinear, h]
    split_ifs <;> rfl

@[simp] theorem mixedLinearMap_apply (P : Parameters K m) (c j : Fin m) (Q : Fin 3 → K) :
    mixedLinearMap P c j Q = P.mixedLinear c Q j := rfl

section C3

open CubicPair CubicPair.RationalConstruction

/-- The mixed lift agrees with the checked rational C.3 coefficient tensor on its basis. -/
theorem c3_mixedLinear_basis (c : Fin 4) (q : Fin 3) (i : Fin 7) (k : Fin 2) :
    c3Parameters.mixedLinear (centerIndex c) (c3Basis q) i k = liftCoefficientsQ c q i k := by
  have hB : Parameters.mixedArray (centerIndex c) (c3Basis q) = c3Mixed c q := by
    funext j r
    by_cases hj : j = centerIndex c <;> simp [Parameters.mixedArray, c3Mixed, c3Basis, hj]
  rw [← c3GraphLiftCoefficients_eq]
  by_cases hci : centerIndex c < i
  · have hic : ¬ i < centerIndex c := not_lt_of_ge hci.le
    simp [Parameters.mixedLinear, Parameters.mixedCubic, Parameters.coefficientLift,
      c3GraphLiftCoefficients, hB, hci, hic]
  · by_cases hic : i < centerIndex c
    · simp [Parameters.mixedLinear, Parameters.mixedCubic, Parameters.coefficientLift,
        c3GraphLiftCoefficients, hB, hci, hic]
    · have heq : i = centerIndex c := le_antisymm (le_of_not_gt hci) (le_of_not_gt hic)
      subst i
      simp [Parameters.mixedLinear, Parameters.mixedCubic, Parameters.coefficientLift,
        c3GraphLiftCoefficients, hB]

/-- The entire rational C.3 correction is the linear combination of the checked basis lifts. -/
theorem c3_mixedLinear_eq_linearLiftQ (c : Fin 4) (Q : Fin 3 → ℚ) (i : Fin 7) (k : Fin 2) :
    c3Parameters.mixedLinear (centerIndex c) Q i k = linearLiftQ Q c i k := by
  have hQ : Q = ∑ q, Q q • c3Basis q := by
    funext r
    simp [Finset.sum_apply, c3Basis, smul_eq_mul, mul_ite]
  calc
    _ = mixedLinearMap c3Parameters (centerIndex c) i (∑ q, Q q • c3Basis q) k :=
      congrArg (fun B => mixedLinearMap c3Parameters (centerIndex c) i B k) hQ
    _ = _ := by
      simp only [map_sum, map_smul]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mixedLinearMap_apply,
        c3_mixedLinear_basis, linearLiftQ]

/-- Agreement on the incident chart transports each C.3 basis coefficient into the larger graph. -/
theorem mixedLinear_eq_c3_coefficients {L : Parameters ℚ m} {ι : Fin 7 ↪ Fin m}
    {hι : StrictMono ι} (c : Fin 4) (h : AgreesAt c3Parameters L ι hι (centerIndex c))
    (q : Fin 3) (i : Fin 7) (k : Fin 2) :
    L.mixedLinear (ι (centerIndex c)) (c3Basis q) (ι i) k = liftCoefficientsQ c q i k :=
  (congrFun (mixedLinear_eq_of_agreesAt h (c3Basis q) i) k).symm.trans (c3_mixedLinear_basis c q i k)

/-- The same local agreement transports every normal quadratic correction. -/
theorem mixedLinear_eq_c3_linearLiftQ {L : Parameters ℚ m} {ι : Fin 7 ↪ Fin m}
    {hι : StrictMono ι} (c : Fin 4) (h : AgreesAt c3Parameters L ι hι (centerIndex c))
    (Q : Fin 3 → ℚ) (i : Fin 7) (k : Fin 2) :
    L.mixedLinear (ι (centerIndex c)) Q (ι i) k = linearLiftQ Q c i k :=
  (congrFun (mixedLinear_eq_of_agreesAt h Q i) k).symm.trans
    (c3_mixedLinear_eq_linearLiftQ c Q i k)

end C3
end IdealGeneration.CubicMixedLocality
