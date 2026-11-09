module

public import IdealGeneration.TwoNormalEuler
public import IdealGeneration.TwoNormalDivision

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The two-slice normal form for Euler kernels

Vanishing tangential restrictions on both coordinate slices forces the
residual form (4.7). All factorizations take place in the polynomial ring.
-/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial Module
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K] (m : ℕ)

/-- Keep the `s` and tangential components and restrict their polynomials. -/
def sliceATuple (d : ℕ) :
    (Fin (m + 2) → Forms K (m + 2) d) →ₗ[K]
      (Fin (m + 1) → Forms K (m + 1) d) :=
  LinearMap.pi fun j : Fin (m + 1) => Fin.cases
    ((restrictAForm K m d).comp (LinearMap.proj (0 : Fin (m + 2))))
    (fun i => (restrictAForm K m d).comp (LinearMap.proj i.succ.succ)) j

@[simp] theorem sliceATuple_zero {d : ℕ} (f : Fin (m + 2) → Forms K (m + 2) d) :
    sliceATuple K m d f 0 = restrictAForm K m d (f 0) := rfl

@[simp] theorem sliceATuple_succ {d : ℕ} (f : Fin (m + 2) → Forms K (m + 2) d)
    (i : Fin m) :
    sliceATuple K m d f i.succ = restrictAForm K m d (f i.succ.succ) := rfl

/-- Restricting the ambient Euler equation gives the first slice equation. -/
theorem sliceATuple_relation (d : ℕ) (f : HyperplaneEuler.Relations K (m + 2) d) :
    formMultiplication K (m + 1) d (sliceATuple K m d f.val) = 0 := by
  apply Subtype.ext
  simp only [formMultiplication_val, Fin.sum_univ_succ, sliceATuple_zero,
    sliceATuple_succ, restrictAForm_val, Submodule.coe_zero]
  have hf := congrArg Subtype.val f.property
  rw [formMultiplication_val, Fin.sum_univ_succ, Fin.sum_univ_succ, Submodule.coe_zero] at hf
  have h := congrArg (restrictA K m) hf
  simpa only [map_add, map_mul, map_sum, restrictA_s, restrictA_t, restrictA_y,
    zero_mul, zero_add, map_zero] using h

/-- Tangential restriction to the slice `t=0`. -/
def sliceARelation (d : ℕ) :
    HyperplaneEuler.Relations K (m + 2) d →ₗ[K] HyperplaneEuler.Relations K (m + 1) d :=
  ((sliceATuple K m d).comp (formMultiplication K (m + 2) d).ker.subtype).codRestrict _
    (sliceATuple_relation K m d)

@[simp] theorem sliceARelation_zero_val {d : ℕ}
    (f : HyperplaneEuler.Relations K (m + 2) d) :
    ((sliceARelation K m d f).val 0).val = restrictA K m (f.val 0).val := rfl

@[simp] theorem sliceARelation_succ_val {d : ℕ}
    (f : HyperplaneEuler.Relations K (m + 2) d) (i : Fin m) :
    ((sliceARelation K m d f).val i.succ).val = restrictA K m (f.val i.succ.succ).val := rfl

/-- Tangential restriction to the slice `s=0`. -/
abbrev sliceBRelation (d : ℕ) := HyperplaneEuler.trace K (m + 1) d

/-- Embed a representative of the `t=0` slice in the ambient coordinates. -/
def sliceARepresentative (y : Fin (m + 1) → K) : Fin (m + 2) → K :=
  Fin.cons (y 0) (Fin.cons 0 (fun i => y i.succ))

/-- Evaluating on the first slice commutes with its polynomial restriction. -/
theorem eval_restrictA (y : Fin (m + 1) → K) (f : Poly K (m + 2)) :
    eval y (restrictA K m f) = eval (sliceARepresentative K m y) f := by
  have h : (eval y).comp (restrictA K m).toRingHom = eval (sliceARepresentative K m y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [RingHom.comp_apply]
        change eval y (restrictA K m (X 0)) = eval (sliceARepresentative K m y) (X 0)
        simp only [restrictA_s, eval_X, sliceARepresentative, Fin.cons_zero]
      · refine Fin.cases ?_ (fun i => ?_) i
        · rw [RingHom.comp_apply]
          change eval y (restrictA K m (X (0 : Fin (m + 1)).succ)) =
            eval (sliceARepresentative K m y) (X (0 : Fin (m + 1)).succ)
          simp only [restrictA_t, map_zero, eval_X, sliceARepresentative,
            Fin.cons_succ, Fin.cons_zero]
        · rw [RingHom.comp_apply]
          change eval y (restrictA K m (X i.succ.succ)) =
            eval (sliceARepresentative K m y) (X i.succ.succ)
          simp only [restrictA_y, eval_X, sliceARepresentative, Fin.cons_succ]
  exact congrArg (fun F : Poly K (m + 2) →+* K => F f) h

/-- Component evaluation of the first slice relation is ambient component evaluation. -/
theorem eval_sliceARelation {d : ℕ} (f : HyperplaneEuler.Relations K (m + 2) d)
    (y : Fin (m + 1) → K) (j : Fin (m + 1)) :
    eval y ((sliceARelation K m d f).val j).val =
      eval (sliceARepresentative K m y)
        (f.val (Fin.cases 0 (fun i : Fin m => i.succ.succ) j)).val := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [sliceARelation_zero_val, Fin.cases_zero, eval_restrictA]
  · simp only [sliceARelation_succ_val, Fin.cases_succ, eval_restrictA]

/-- Component evaluation of the second slice relation is ambient component evaluation. -/
theorem eval_sliceBRelation {d : ℕ} (f : HyperplaneEuler.Relations K (m + 2) d)
    (y : Fin (m + 1) → K) (j : Fin (m + 1)) :
    eval y ((sliceBRelation K m d f).val j).val =
      eval (Fin.cons 0 y) (f.val j.succ).val :=
  eval_hyperplaneRestrict K (m + 1) (f.val j.succ).val y

/-- The tangential Euler relations induced on the common trace agree. -/
theorem sliceRelations_trace_eq {d : ℕ} (f : HyperplaneEuler.Relations K (m + 2) d) :
    HyperplaneEuler.trace K m d (sliceARelation K m d f) =
      HyperplaneEuler.trace K m d (sliceBRelation K m d f) := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  simpa only [HyperplaneEuler.trace_apply, restrictForm_val, sliceARelation_succ_val,
    restrictTrace, AlgHom.comp_apply] using restrictA_trace K m (f.val i.succ.succ).val

/-- Vanishing tangent restrictions on both slices gives exactly (4.7). -/
theorem exists_residualEuler_of_slice_zero (d : ℕ)
    (f : (formMultiplication K (m + 2) (d + 1 + 1)).ker)
    (hAs : restrictA K m (f.val 0).val = 0)
    (hBt : hyperplaneRestrict K (m + 1) (f.val (0 : Fin (m + 1)).succ).val = 0)
    (hAy : ∀ i : Fin m, restrictA K m (f.val i.succ.succ).val = 0)
    (hBy : ∀ i : Fin m, hyperplaneRestrict K (m + 1) (f.val i.succ.succ).val = 0) :
    ∃ z : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1),
      residualEuler K m d z = f := by
  have hcoeff (i : Fin m) : ∃ a : Forms K (m + 2) d,
      (f.val i.succ.succ).val = X 0 * (X (0 : Fin (m + 1)).succ * a.val) :=
    exists_double_normal_factor K m (d := d) (f.val i.succ.succ) (hAy i) (hBy i)
  choose a ha using hcoeff
  obtain ⟨h, hh⟩ := (restrictA_eq_zero_iff K m (d := d + 1) (f.val 0)).mp hAs
  obtain ⟨b, hb⟩ := (restrictForm_eq_zero_iff K (m + 1) (d := d + 1)
    (f.val (0 : Fin (m + 1)).succ)).mp (Subtype.ext hBt)
  have heuler := congrArg Subtype.val f.property
  change (∑ j, X j * (f.val j).val) = 0 at heuler
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at heuler
  simp only [hh, hb, ha] at heuler
  have hsum : (∑ i, X i.succ.succ *
      (X 0 * (X (0 : Fin (m + 1)).succ * (a i).val))) =
      X 0 * X (0 : Fin (m + 1)).succ *
        (∑ i, X i.succ.succ * (a i).val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at heuler
  have hfactor : X 0 * X (0 : Fin (m + 1)).succ *
      (h.val + b.val + (tangentProduct K m d a).val) = 0 := by
    rw [tangentProduct_val]
    linear_combination heuler
  have hrelation : h.val + b.val + (tangentProduct K m d a).val = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
  have hb' : b.val = (-h - tangentProduct K m d a).val := by
    change b.val = -h.val - (tangentProduct K m d a).val
    linear_combination hrelation
  refine ⟨(a, h), ?_⟩
  apply Subtype.ext
  funext j
  apply Subtype.ext
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hh.symm
  · refine Fin.cases ?_ (fun i => ?_) i
    · change X 0 * (-h - tangentProduct K m d a).val =
        (f.val (0 : Fin (m + 1)).succ).val
      rw [hb, hb']
    · exact (ha i).symm

/-- Zero Euler restrictions on both slices force the residual normal form. -/
theorem exists_residualEuler_of_slice_relations_zero (d : ℕ)
    (f : HyperplaneEuler.Relations K (m + 2) (d + 1 + 1))
    (hA : sliceARelation K m (d + 1 + 1) f = 0)
    (hB : sliceBRelation K m (d + 1 + 1) f = 0) :
    ∃ z : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1),
      residualEuler K m d z = f := by
  apply exists_residualEuler_of_slice_zero K m d f
  · have h := congrArg (fun F : HyperplaneEuler.Relations K (m + 1) (d + 1 + 1) =>
      (F.val 0).val) hA
    simpa only [sliceARelation_zero_val, Submodule.coe_zero, Pi.zero_apply] using h
  · exact congrArg (fun F : HyperplaneEuler.Relations K (m + 1) (d + 1 + 1) =>
      (F.val 0).val) hB
  · intro i
    have h := congrArg (fun F : HyperplaneEuler.Relations K (m + 1) (d + 1 + 1) =>
      (F.val i.succ).val) hA
    simpa only [sliceARelation_succ_val, Submodule.coe_zero, Pi.zero_apply] using h
  · intro i
    exact congrArg (fun F : HyperplaneEuler.Relations K (m + 1) (d + 1 + 1) =>
      (F.val i.succ).val) hB

/-- Away from both normal hyperplanes, vanishing of the Euler tuple is
exactly vanishing of its free residual coefficients. -/
theorem residualEuler_vanishing_iff (d : ℕ)
    (z : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1))
    (x : Fin (m + 2) → K) (hs : x 0 ≠ 0) (ht : x (0 : Fin (m + 1)).succ ≠ 0) :
    (∀ j, eval x ((residualEuler K m d z).val j).val = 0) ↔
      (∀ i, eval x (z.1 i).val = 0) ∧ eval x z.2.val = 0 := by
  constructor
  · intro h
    constructor
    · intro i
      have hi := h i.succ.succ
      change eval x (X 0 * (X (0 : Fin (m + 1)).succ * (z.1 i).val)) = 0 at hi
      simp only [map_mul, eval_X] at hi
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hs)).resolve_left ht
    · have hh := h 0
      change eval x (X (0 : Fin (m + 1)).succ * z.2.val) = 0 at hh
      simp only [map_mul, eval_X] at hh
      exact (mul_eq_zero.mp hh).resolve_left ht
  · rintro ⟨ha, hh⟩ j
    refine Fin.cases ?_ (fun j => ?_) j
    · change eval x (X (0 : Fin (m + 1)).succ * z.2.val) = 0
      simp [hh]
    · refine Fin.cases ?_ (fun i => ?_) j
      · change eval x (X 0 * (-z.2.val - ∑ i, X i.succ.succ * (z.1 i).val)) = 0
        simp [ha, hh]
      · change eval x (X 0 * (X (0 : Fin (m + 1)).succ * (z.1 i).val)) = 0
        simp [ha]

/-- The ambient kernel coefficients belong to the actual lower-degree
point ideals at the off-slice group. -/
theorem exists_residualEuler_in_pointIdeals {p : ℕ} (d : ℕ)
    (x : PointCoordinates K (m + 1) p)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (f : (formMultiplication K (m + 2) (d + 1 + 1)).ker)
    (hAs : restrictA K m (f.val 0).val = 0)
    (hBt : hyperplaneRestrict K (m + 1) (f.val (0 : Fin (m + 1)).succ).val = 0)
    (hAy : ∀ i : Fin m, restrictA K m (f.val i.succ.succ).val = 0)
    (hBy : ∀ i : Fin m, hyperplaneRestrict K (m + 1) (f.val i.succ.succ).val = 0)
    (hx : ∀ i j, eval (chartPoint K x i) (f.val j).val = 0) :
    ∃ (a : Fin m → pointDegreePiece K x d) (h : pointDegreePiece K x (d + 1)),
      residualEuler K m d ((fun i => (a i).val), h.val) = f := by
  obtain ⟨z, hz⟩ := exists_residualEuler_of_slice_zero K m d f hAs hBt hAy hBy
  have hv (i : Fin p) := (residualEuler_vanishing_iff K m d z (chartPoint K x i)
    (hs i) (ht i)).mp (by simpa only [hz] using hx i)
  have ha : ∀ j, z.1 j ∈ pointDegreePiece K x d := by
    intro j
    rw [mem_pointDegreePiece]
    exact fun i => (hv i).1 j
  have hh : z.2 ∈ pointDegreePiece K x (d + 1) := by
    rw [mem_pointDegreePiece]
    exact fun i => (hv i).2
  exact ⟨fun j => ⟨z.1 j, ha j⟩, ⟨z.2, hh⟩, hz⟩

end IdealGeneration.TwoNormalTrace
