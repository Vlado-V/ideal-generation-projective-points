module

public import IdealGeneration.FractionalRegroup
public import IdealGeneration.RepresentativeNormalization

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Coordinate enumerations for regrouped fractional configurations

The finite sum of full-point indices and the complementary trace indices are
enumerated by the exact point counts. Every representative is normalized in
the final coordinate before entering the usual affine coordinate spaces.
-/

noncomputable section
namespace IdealGeneration.FractionalRegroupCoordinates
open MvPolynomial HyperplaneEuler DifferentialPoint FractionalResidual FractionalRegroup
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

/-- Enumerate a finite indexed family of representatives by a prescribed count. -/
def orderedRepresentatives {I : Type*} [Fintype I] {m p : ℕ}
    (z : I → Fin (m + 1) → K) (hcard : Fintype.card I = p) :
    Fin p → Fin (m + 1) → K :=
  fun i => z ((Fintype.equivFinOfCardEq hcard).symm i)

/-- Normalizing already normalized representatives recovers them exactly. -/
theorem chartPoint_normalized_eq {m p : ℕ} (z : Fin p → Fin (m + 1) → K)
    (hz : ∀ i, z i (Fin.last m) = 1) (i : Fin p) :
    chartPoint K (normalizedCoordinates z) i = z i := by
  have hs := normalizedCoordinates_scale z (fun j => by rw [hz j]; exact one_ne_zero) i
  simpa only [hz i, one_mul] using hs

/-- Enumeration and normalization preserve all full Euler value conditions. -/
theorem ordered_full_conditions_iff {I : Type*} [Fintype I] {m p d : ℕ}
    (z : I → Fin (m + 1) → K) (hcard : Fintype.card I = p)
    (hz : ∀ i, z i (Fin.last m) = 1) (f : Relations K (m + 1) d) :
    (∀ i : Fin p, vectorEvaluation
      (chartPoint K (normalizedCoordinates (orderedRepresentatives z hcard)) i) f = 0) ↔
      ∀ i : I, vectorEvaluation (z i) f = 0 := by
  let e := Fintype.equivFinOfCardEq hcard
  have hz' : ∀ i, orderedRepresentatives z hcard i (Fin.last m) = 1 :=
    fun i => hz (e.symm i)
  simp_rw [chartPoint_normalized_eq _ hz']
  constructor
  · intro h i
    have hi := h (e i)
    simpa only [orderedRepresentatives, e, Equiv.symm_apply_apply] using hi
  · intro h i
    exact h (e.symm i)

/-- The exact enumeration of the full-point sum index. -/
def fullIndexEquiv {p z : ℕ} (s : Finset (Fin p)) :
    (Fin z ⊕ (s ⊕ Unit)) ≃ Fin (z + s.card + 1) :=
  Fintype.equivFinOfCardEq (by simpa using regroupedFullPoints_card (O := Fin z) s)

/-- A canonical moving representative with its final coordinate equal to one. -/
def canonicalMoved {n : ℕ} (t : K) (y : Fin n → K) : Fin (n + 2) → K :=
  Fin.cons t (Fin.snoc y 1)

@[simp] theorem canonicalMoved_last {n : ℕ} (t : K) (y : Fin n → K) :
    canonicalMoved t y (Fin.last (n + 1)) = 1 := by
  simp [canonicalMoved]

@[simp] theorem canonicalMoved_zero {n : ℕ} (t : K) (y : Fin n → K) :
    canonicalMoved t y 0 = t := by
  simp [canonicalMoved]

/-- The canonical representative is the affine line with unit normal velocity. -/
theorem canonicalMoved_eq_line {n : ℕ} (t : K) (y : Fin n → K) :
    canonicalMoved t y = fun j =>
      (Fin.cons 0 (Fin.snoc y 1) : Fin (n + 2) → K) j +
        t * (Fin.cons 1 (fun _ => 0) : Fin (n + 2) → K) j := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [canonicalMoved]

/-- The exact-count full representatives used by the affine model. -/
def fullRepresentatives {n p z : ℕ} (a : PointCoordinates K (n + 1) z)
    (P : PointCoordinates K n p) (s : Finset (Fin p)) (t : K) (y : Fin n → K) :
    Fin (z + s.card + 1) → Fin (n + 2) → K :=
  orderedRepresentatives
    (regroupedFullPoints (fun j => chartPoint K a j) P s (canonicalMoved t y))
    (by simpa using regroupedFullPoints_card (O := Fin z) s)

/-- Affine coordinates of the enumerated full-point configuration. -/
def fullCoordinates {n p z : ℕ} (a : PointCoordinates K (n + 1) z)
    (P : PointCoordinates K n p) (s : Finset (Fin p)) (t : K) (y : Fin n → K) :
    PointCoordinates K (n + 1) (z + s.card + 1) :=
  normalizedCoordinates (fullRepresentatives a P s t y)

/-- Every full representative has final coordinate one, including the moving point. -/
theorem regroupedFullPoints_last {n p z : ℕ} (a : PointCoordinates K (n + 1) z)
    (P : PointCoordinates K n p) (s : Finset (Fin p)) (t : K) (y : Fin n → K)
    (i : Fin z ⊕ (s ⊕ Unit)) :
    regroupedFullPoints (fun j => chartPoint K a j) P s (canonicalMoved t y) i
      (Fin.last (n + 1)) = 1 := by
  rcases i with i | i
  · simp [regroupedFullPoints]
  · rcases i with i | i
    · simp [regroupedFullPoints, selectedPoints]
    · simp [regroupedFullPoints]

/-- The affine chart point is the original full representative at the enumerated index. -/
theorem fullCoordinates_chartPoint {n p z : ℕ} (a : PointCoordinates K (n + 1) z)
    (P : PointCoordinates K n p) (s : Finset (Fin p)) (t : K) (y : Fin n → K)
    (i : Fin (z + s.card + 1)) :
    chartPoint K (fullCoordinates a P s t y) i =
      regroupedFullPoints (fun j => chartPoint K a j) P s (canonicalMoved t y)
        ((fullIndexEquiv (z := z) s).symm i) := by
  exact chartPoint_normalized_eq (fullRepresentatives a P s t y)
    (fun j => regroupedFullPoints_last a P s t y _) i

/-- Full point conditions in ordinary coordinates are exactly the regrouped conditions. -/
theorem fullCoordinates_conditions_iff {n p z d : ℕ} (a : PointCoordinates K (n + 1) z)
    (P : PointCoordinates K n p) (s : Finset (Fin p)) (t : K) (y : Fin n → K)
    (f : Relations K (n + 2) d) :
    (∀ i, vectorEvaluation (chartPoint K (fullCoordinates a P s t y) i) f = 0) ↔
      ∀ i : Fin z ⊕ (s ⊕ Unit), vectorEvaluation
        (regroupedFullPoints (fun j => chartPoint K a j) P s (canonicalMoved t y) i) f = 0 := by
  exact ordered_full_conditions_iff
    (regroupedFullPoints (fun j => chartPoint K a j) P s (canonicalMoved t y))
    (by simpa using regroupedFullPoints_card (O := Fin z) s)
    (regroupedFullPoints_last a P s t y) f

/-- The exact enumeration of the complementary trace indices. -/
def complementIndexEquiv {p : ℕ} (s : Finset (Fin p)) :
    (↥(Finset.univ \ s)) ≃ Fin (p - s.card) :=
  Fintype.equivFinOfCardEq (unselectedTrace_card s)

/-- Complementary trace points in the standard affine coordinate format. -/
def complementCoordinates {n p : ℕ} (P : PointCoordinates K n p)
    (s : Finset (Fin p)) : PointCoordinates K n (p - s.card) :=
  fun ij => P (((complementIndexEquiv s).symm ij.1).val, ij.2)

/-- Enumerating the complementary trace points preserves their representatives. -/
theorem complementCoordinates_chartPoint {n p : ℕ} (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (i : Fin (p - s.card)) :
    chartPoint K (complementCoordinates P s) i =
      chartPoint K P (((complementIndexEquiv s).symm i).val) := rfl

/-- Complementary trace evaluation is exactly evaluation at the original unselected indices. -/
theorem complementCoordinates_conditions_iff {n p d : ℕ} (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (f : Relations K (n + 1) d) :
    (∀ i, vectorEvaluation (chartPoint K (complementCoordinates P s) i) f = 0) ↔
      ∀ i ∈ Finset.univ \ s, vectorEvaluation (chartPoint K P i) f = 0 := by
  simp_rw [complementCoordinates_chartPoint]
  constructor
  · intro h i hi
    have hz := h (complementIndexEquiv s ⟨i, hi⟩)
    simpa only [Equiv.symm_apply_apply] using hz
  · intro h i
    exact h _ ((complementIndexEquiv s).symm i).property

/-- The extra partial trace condition remains identical under complement enumeration. -/
theorem complementCoordinates_tracePointSpace_iff {n p d : ℕ}
    (P : PointCoordinates K n p) (s : Finset (Fin p))
    (C : Submodule K (Relations K (n + 1) d)) (f : Relations K (n + 1) d) :
    f ∈ tracePointSpace C P (Finset.univ \ s) ↔
      f ∈ C ∧ ∀ i, vectorEvaluation (chartPoint K (complementCoordinates P s) i) f = 0 := by
  change (f ∈ C ∧ ∀ i ∈ Finset.univ \ s, vectorEvaluation (chartPoint K P i) f = 0) ↔ _
  rw [complementCoordinates_conditions_iff]

/-- The complementary trace subspace is unchanged by its coordinate enumeration. -/
theorem complement_tracePointSpace_eq {n p d : ℕ}
    (P : PointCoordinates K n p) (s : Finset (Fin p))
    (C : Submodule K (Relations K (n + 1) d)) :
    tracePointSpace C (complementCoordinates P s) Finset.univ =
      tracePointSpace C P (Finset.univ \ s) := by
  ext f
  change (f ∈ C ∧ ∀ i ∈ Finset.univ,
    vectorEvaluation (chartPoint K (complementCoordinates P s) i) f = 0) ↔ _
  simp only [Finset.mem_univ, forall_true_left]
  rw [complementCoordinates_conditions_iff]
  rfl

/-- The normalized full and complementary trace coordinates realize the exact regrouped kernel. -/
theorem normalized_regrouped_space_eq {n p z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (t : K) (y : Fin n → K)
    (C : Submodule K (Relations K (n + 1) (d + 1))) :
    fixedSpace (fun i => chartPoint K (fullCoordinates a P s t y) i) noPoints
        (tracePointSpace C (complementCoordinates P s) Finset.univ) =
      fixedSpace (fun i => chartPoint K a i) (selectedPoints P s)
          (tracePointSpace C P Finset.univ) ⊓
        (vectorEvaluation (canonicalMoved t y)).ker := by
  rw [selected_points_regroup, complement_tracePointSpace_eq]
  ext f
  change (trace K (n + 1) (d + 1) f ∈ tracePointSpace C P (Finset.univ \ s) ∧
      (∀ i, vectorEvaluation (chartPoint K (fullCoordinates a P s t y) i) f = 0) ∧
      (∀ i : Empty, vectorEvaluation (noPoints i) f = 0)) ↔
    (trace K (n + 1) (d + 1) f ∈ tracePointSpace C P (Finset.univ \ s) ∧
      (∀ i, vectorEvaluation
        (regroupedFullPoints (fun j => chartPoint K a j) P s (canonicalMoved t y) i) f = 0) ∧
      (∀ i : Empty, vectorEvaluation (noPoints i) f = 0))
  rw [fullCoordinates_conditions_iff]

end IdealGeneration.FractionalRegroupCoordinates
