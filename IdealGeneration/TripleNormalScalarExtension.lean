module

public import IdealGeneration.RepresentativeGeneric
public import IdealGeneration.DeformationMatrix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Scalar postulation under the three-variable enlargement

Old trace variables are followed by the three new base variables and then
the four layer variables. New coordinate points, old–new edge points, and
new layer points each admit explicit quadratic corrections.
-/

noncomputable section
namespace IdealGeneration.TripleNormal

open MvPolynomial Module

variable {K : Type*} [Field K] {h p q : ℕ}

private def oldBaseIndex (i : Fin h) : Fin (h + 3 + 4) :=
  (i.castAdd 3).castAdd 4

private def newBaseIndex (b : Fin 3) : Fin (h + 3 + 4) :=
  (b.natAdd h).castAdd 4

private def layerIndex (j : Fin 4) : Fin (h + 3 + 4) :=
  j.natAdd (h + 3)

/-- Coordinate inclusion of the old trace, skipping the three new base variables. -/
def oldTraceIndex (h : ℕ) : Fin (h + 4) → Fin (h + 3 + 4) :=
  Fin.addCases oldBaseIndex layerIndex

/-- The old trace in the enlarged space, with all new base coordinates zero. -/
def embedOldTrace (x : Fin (h + 4) → K) : Fin (h + 3 + 4) → K :=
  Fin.append (Fin.append (fun i : Fin h => x (i.castAdd 4)) 0) (fun j : Fin 4 => x (j.natAdd h))

/-- The three new coordinate points. -/
def extensionCoordinate (h : ℕ) (b : Fin 3) : Fin (h + 3 + 4) → K :=
  Fin.append (Fin.append (0 : Fin h → K) (Pi.single b 1)) (0 : Fin 4 → K)

/-- The new free points lie on the enlarged base. -/
def extensionFreePoint (x : Fin (h + 3) → K) : Fin (h + 3 + 4) → K :=
  Fin.append x (0 : Fin 4 → K)

/-- Each new layer point has all new base coordinates one and one nonzero layer coordinate. -/
def extensionLayer (h : ℕ) (ζ : Fin 4 → K) (j : Fin 4) : Fin (h + 3 + 4) → K :=
  Fin.append (Fin.append (0 : Fin h → K) (fun _ : Fin 3 => 1)) (Pi.single j (ζ j))

/-- The four trace groups in enlargement order. -/
def extensionTracePoints (z : Fin p → Fin (h + 4) → K)
    (a : Fin q × Fin (h + 3) → K) (ζ : Fin 4 → K) :
    Fin (p + (3 + (q + 4))) → Fin (h + 3 + 4) → K :=
  Fin.append (embedOldTrace ∘ z)
    (Fin.append (extensionCoordinate h)
      (Fin.append (fun i => extensionFreePoint (fun j => a (i, j))) (extensionLayer h ζ)))

private def edgeCoordinates (e : Fin q ↪ Fin h × Fin 3) : Fin q × Fin (h + 3) → K :=
  fun ij => Fin.append (Pi.single (e ij.1).1 1) (Pi.single (e ij.1).2 1) ij.2

private def coordinateProduct {n : ℕ} (i j : Fin n) : Forms K n 2 :=
  ⟨X i * X j, (isHomogeneous_X K i).mul (isHomogeneous_X K j)⟩

@[simp] private theorem evaluationLinear_coordinateProduct {n : ℕ} (x : Fin n → K)
    (i j : Fin n) :
    evaluationLinear K n 2 x (coordinateProduct i j) = x i * x j := by
  simp [evaluationLinear, coordinateProduct]

@[simp] theorem embedOldTrace_oldTraceIndex (x : Fin (h + 4) → K) :
    embedOldTrace x ∘ oldTraceIndex h = x := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp [oldTraceIndex, oldBaseIndex, embedOldTrace]
  · simp [oldTraceIndex, layerIndex, embedOldTrace]

private theorem edgeEvaluation (e : Fin q ↪ Fin h × Fin 3) (i j : Fin q) :
    evaluationLinear K (h + 3 + 4) 2
        (extensionFreePoint (fun k => edgeCoordinates (K := K) e (i, k)))
        (coordinateProduct (oldBaseIndex (e j).1) (newBaseIndex (e j).2)) =
      if i = j then 1 else 0 := by
  classical
  simp only [evaluationLinear_coordinateProduct, extensionFreePoint, oldBaseIndex, newBaseIndex,
    edgeCoordinates, Fin.append_left, Fin.append_right, Pi.single_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hne : e j ≠ e i := fun he => hij (e.injective he).symm
    by_cases hfirst : (e j).1 = (e i).1
    · have hsecond : (e j).2 ≠ (e i).2 := fun he => hne (Prod.ext hfirst he)
      simp [hfirst, hsecond, hij]
    · simp [hfirst, hij]

/-- The edge-point specialization gives full row rank for the actual enlarged trace. -/
private theorem extensionTraceEvaluation_surjective_edges
    (z : Fin p → Fin (h + 4) → K) (ζ : Fin 4 → K)
    (e : Fin q ↪ Fin h × Fin 3) (hζ : ∀ j, ζ j ≠ 0)
    (hOld : Function.Surjective (representativeEvaluation K z 2)) :
    Function.Surjective (representativeEvaluation K
      (extensionTracePoints z (edgeCoordinates e) ζ) 2) := by
  classical
  intro target
  let oldValue (i : Fin p) := target (i.castAdd (3 + (q + 4)))
  let coordValue (i : Fin 3) := target ((i.castAdd (q + 4)).natAdd p)
  let freeValue (i : Fin q) := target (((i.castAdd 4).natAdd 3).natAdd p)
  let layerValue (j : Fin 4) := target (((j.natAdd q).natAdd 3).natAdd p)
  obtain ⟨f, hf⟩ := hOld oldValue
  let F₀ : Forms K (h + 3 + 4) 2 :=
    ⟨rename (oldTraceIndex h) f.val, f.property.rename_isHomogeneous⟩
  let E := evaluationLinear K (h + 3 + 4) 2
  let coord := extensionCoordinate (K := K) h
  let free (i : Fin q) :=
    extensionFreePoint (fun j => edgeCoordinates (K := K) e (i, j))
  let layer := extensionLayer h ζ
  let A (b : Fin 3) := coordinateProduct (K := K) (newBaseIndex (h := h) b) (newBaseIndex b)
  let B (i : Fin q) := coordinateProduct (K := K) (oldBaseIndex (e i).1) (newBaseIndex (e i).2)
  let C (j : Fin 4) := (ζ j)⁻¹ •
    coordinateProduct (K := K) (newBaseIndex (h := h) 0) (layerIndex j)
  have hA (i b : Fin 3) : E (coord i) (A b) = if i = b then 1 else 0 := by
    change evaluationLinear K _ _ (coord i)
      (coordinateProduct (newBaseIndex b) (newBaseIndex b)) = _
    rw [evaluationLinear_coordinateProduct]
    by_cases hib : i = b
    · subst b
      simp [coord, extensionCoordinate, newBaseIndex]
    · simp [coord, extensionCoordinate, newBaseIndex, Ne.symm hib, hib]
  have hB (i j : Fin q) : E (free i) (B j) = if i = j then 1 else 0 :=
    edgeEvaluation e i j
  have hC (i j : Fin 4) : E (layer i) (C j) = if i = j then 1 else 0 := by
    change evaluationLinear K _ _ (layer i)
      ((ζ j)⁻¹ • coordinateProduct (newBaseIndex 0) (layerIndex j)) = _
    rw [map_smul, evaluationLinear_coordinateProduct]
    by_cases hij : i = j
    · subst j
      simp [layer, extensionLayer, newBaseIndex, layerIndex, hζ]
    · simp [layer, extensionLayer, newBaseIndex, layerIndex, Ne.symm hij, hij]
  have hOldA (i : Fin p) (b : Fin 3) : E (embedOldTrace (z i)) (A b) = 0 := by
    change evaluationLinear K _ _ (embedOldTrace (z i))
      (coordinateProduct (newBaseIndex b) (newBaseIndex b)) = 0
    rw [evaluationLinear_coordinateProduct]
    simp [embedOldTrace, newBaseIndex]
  have hOldB (i : Fin p) (j : Fin q) : E (embedOldTrace (z i)) (B j) = 0 := by
    change evaluationLinear K _ _ (embedOldTrace (z i))
      (coordinateProduct (oldBaseIndex (e j).1) (newBaseIndex (e j).2)) = 0
    rw [evaluationLinear_coordinateProduct]
    simp [embedOldTrace, newBaseIndex]
  have hOldC (i : Fin p) (j : Fin 4) : E (embedOldTrace (z i)) (C j) = 0 := by
    change evaluationLinear K _ _ (embedOldTrace (z i))
      ((ζ j)⁻¹ • coordinateProduct (newBaseIndex 0) (layerIndex j)) = 0
    rw [map_smul, evaluationLinear_coordinateProduct]
    simp [embedOldTrace, newBaseIndex]
  have hCoordB (i : Fin 3) (j : Fin q) : E (coord i) (B j) = 0 := by
    change evaluationLinear K _ _ (coord i)
      (coordinateProduct (oldBaseIndex (e j).1) (newBaseIndex (e j).2)) = 0
    rw [evaluationLinear_coordinateProduct]
    simp [coord, extensionCoordinate, oldBaseIndex]
  have hCoordC (i : Fin 3) (j : Fin 4) : E (coord i) (C j) = 0 := by
    change evaluationLinear K _ _ (coord i)
      ((ζ j)⁻¹ • coordinateProduct (newBaseIndex 0) (layerIndex j)) = 0
    rw [map_smul, evaluationLinear_coordinateProduct]
    simp [coord, extensionCoordinate, layerIndex]
  have hFreeC (i : Fin q) (j : Fin 4) : E (free i) (C j) = 0 := by
    change evaluationLinear K _ _ (free i)
      ((ζ j)⁻¹ • coordinateProduct (newBaseIndex 0) (layerIndex j)) = 0
    rw [map_smul, evaluationLinear_coordinateProduct]
    simp [free, extensionFreePoint, layerIndex]
  let F₁ := F₀ + ∑ b, (coordValue b - E (coord b) F₀) • A b
  let F₂ := F₁ + ∑ i, (freeValue i - E (free i) F₁) • B i
  let F₃ := F₂ + ∑ j, (layerValue j - E (layer j) F₂) • C j
  have hEvalOld (i : Fin p) : E (embedOldTrace (z i)) F₃ = oldValue i := by
    have h₀ : E (embedOldTrace (z i)) F₀ = oldValue i := by
      change eval (embedOldTrace (z i)) (rename (oldTraceIndex h) f.val) = oldValue i
      rw [eval_rename, embedOldTrace_oldTraceIndex]
      exact congrFun hf i
    simpa only [F₃, F₂, F₁, map_add, map_sum, map_smul, hOldA, hOldB, hOldC,
      smul_zero, Finset.sum_const_zero, add_zero] using h₀
  have hEvalCoord (i : Fin 3) : E (coord i) F₃ = coordValue i := by
    simp [F₃, F₂, F₁, map_sum, hA, hCoordB, hCoordC, mul_ite]
  have hEvalFree (i : Fin q) : E (free i) F₃ = freeValue i := by
    simp [F₃, F₂, map_sum, hB, hFreeC, mul_ite]
  have hEvalLayer (j : Fin 4) : E (layer j) F₃ = layerValue j := by
    simp [F₃, map_sum, hC, mul_ite]
  refine ⟨F₃, ?_⟩
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [representativeEvaluation, LinearMap.pi_apply, extensionTracePoints, Fin.append_left]
    change E (embedOldTrace (z j)) F₃ = oldValue j
    exact hEvalOld j
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [representativeEvaluation, LinearMap.pi_apply, extensionTracePoints,
        Fin.append_right, Fin.append_left] using hEvalCoord k
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) k
      · simpa only [representativeEvaluation, LinearMap.pi_apply, extensionTracePoints,
          Fin.append_right, Fin.append_left] using hEvalFree l
      · simpa only [representativeEvaluation, LinearMap.pi_apply, extensionTracePoints,
          Fin.append_right] using hEvalLayer l

private theorem extensionTraceEvaluation_polynomial
    (z : Fin p → Fin (h + 4) → K) (ζ : Fin 4 → K) :
    IsPolynomialFamily (fun a : Fin q × Fin (h + 3) → K =>
      representativeEvaluation K (extensionTracePoints z a ζ) 2) := by
  apply isPolynomialFamily_linearMap
  intro f
  apply DeformationMatrix.isPolynomialFamily_pi
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [representativeEvaluation, LinearMap.pi_apply, extensionTracePoints, Fin.append_left]
    exact isPolynomialFamily_const _
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [representativeEvaluation, LinearMap.pi_apply, extensionTracePoints,
        Fin.append_right, Fin.append_left]
      exact isPolynomialFamily_const _
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) k
      · let v : Fin (h + 3 + 4) → MvPolynomial (Fin q × Fin (h + 3)) K :=
          Fin.append (fun j : Fin (h + 3) => X (l, j)) (0 : Fin 4 → _)
        let P := eval₂ C v f.val
        have hP (a : Fin q × Fin (h + 3) → K) :
            eval a P = eval (extensionFreePoint (fun j => a (l, j))) f.val := by
          change eval a (eval₂ C v f.val) = _
          rw [eval_eval₂]
          have hc : (eval a).comp C = RingHom.id K := by ext c; simp
          rw [hc]
          congr 1
          funext j
          refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
            simp [v, extensionFreePoint]
        simp only [representativeEvaluation, LinearMap.pi_apply, extensionTracePoints,
          Fin.append_right, Fin.append_left]
        change IsPolynomialFamily (fun a : Fin q × Fin (h + 3) → K =>
          eval (extensionFreePoint (fun j => a (l, j))) f.val)
        rw [← funext hP]
        exact isPolynomialFamily_eval P
      · simp only [representativeEvaluation, LinearMap.pi_apply, extensionTracePoints,
          Fin.append_right]
        exact isPolynomialFamily_const _

/-- In Appendix A.4 the scalar surjectivity condition holds on a nonempty
principal open of the new free base points. All other trace points stay fixed. -/
theorem extensionTraceEvaluation_surjective_open
    (z : Fin p → Fin (h + 4) → K) (ζ : Fin 4 → K) (hh : 8 ≤ h)
    (hζ : ∀ j, ζ j ≠ 0)
    (hOld : Function.Surjective (representativeEvaluation K z 2)) :
    ∃ P : MvPolynomial (Fin (2 * h + 5) × Fin (h + 3)) K,
      (∃ a, eval a P ≠ 0) ∧ ∀ a, eval a P ≠ 0 →
        Function.Surjective (representativeEvaluation K (extensionTracePoints z a ζ) 2) := by
  let e : Fin (2 * h + 5) ↪ Fin h × Fin 3 :=
    (Fin.castLEEmb (by omega : 2 * h + 5 ≤ h * 3)).trans finProdFinEquiv.symm.toEmbedding
  let a₀ := edgeCoordinates (K := K) e
  let E := fun a : Fin (2 * h + 5) × Fin (h + 3) → K =>
    representativeEvaluation K (extensionTracePoints z a ζ) 2
  have h₀ : Function.Surjective (E a₀) :=
    extensionTraceEvaluation_surjective_edges z ζ e hζ hOld
  obtain ⟨P, hP, hrank⟩ := rank_polynomial_principal_open E
    (extensionTraceEvaluation_polynomial z ζ) a₀
  refine ⟨P, ⟨a₀, hP⟩, fun a ha => ?_⟩
  have hr := hrank a ha
  rw [LinearMap.range_eq_top.mpr h₀, finrank_top] at hr
  exact LinearMap.range_eq_top.mp
    (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hr))

end IdealGeneration.TripleNormal
