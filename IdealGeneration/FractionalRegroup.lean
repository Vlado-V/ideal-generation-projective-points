module

public import IdealGeneration.FractionalResidual

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Regrouping selected hyperplane points

Once a scalar row is selected, its hyperplane point becomes a full point.
The unselected points retain their trace conditions, and the fixed additional
trace subspace is preserved.
-/

noncomputable section
namespace IdealGeneration.FractionalRegroup
open MvPolynomial HyperplaneEuler DifferentialPoint FractionalResidual
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

/-- Impose a subset of the point trace conditions in addition to a fixed trace subspace. -/
def tracePointSpace {n p d : ℕ} (C : Submodule K (Relations K (n + 1) d))
    (P : PointCoordinates K n p) (I : Finset (Fin p)) :
    Submodule K (Relations K (n + 1) d) where
  carrier := {f | f ∈ C ∧ ∀ i ∈ I, vectorEvaluation (chartPoint K P i) f = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    refine ⟨C.add_mem hf.1 hg.1, ?_⟩
    intro i hi
    rw [map_add, hf.2 i hi, hg.2 i hi, add_zero]
  smul_mem' := by
    intro c f hf
    refine ⟨C.smul_mem c hf.1, ?_⟩
    intro i hi
    rw [map_smul, hf.2 i hi, smul_zero]

/-- Full points after the selected rows and the moving point are regrouped. -/
def regroupedFullPoints {n p : ℕ} {O : Type*}
    (off : O → Fin (n + 2) → K) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (moved : Fin (n + 2) → K) :
    O ⊕ (s ⊕ Unit) → Fin (n + 2) → K :=
  Sum.elim off (Sum.elim (selectedPoints P s) (fun _ => moved))

/-- There are no additional full hyperplane points after regrouping. -/
def noPoints {n : ℕ} : Empty → Fin n → K := fun i => nomatch i

/-- A zero full value on the hyperplane has zero trace value there. -/
theorem trace_evaluation_zero_of_selected_zero {n p d : ℕ}
    (P : PointCoordinates K n p) (s : Finset (Fin p)) (i : s)
    (f : Relations K (n + 2) d)
    (hf : vectorEvaluation (selectedPoints P s i) f = 0) :
    vectorEvaluation (chartPoint K P i.val) (trace K (n + 1) d f) = 0 := by
  ext j
  have ht := trace_evaluation (selectedPoints P s i) (by rfl) f j
  have hz := ht.trans (congrFun hf j.succ)
  simpa only [selectedPoints, Fin.cons_succ, Pi.zero_apply] using hz

/-- The selected full points, complementary traces, and moving full point give
exactly the original fixed-space conditions together with the moving value. -/
theorem selected_points_regroup {n p d : ℕ} {O : Type*}
    (off : O → Fin (n + 2) → K) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (moved : Fin (n + 2) → K)
    (C : Submodule K (Relations K (n + 1) (d + 1))) :
    fixedSpace off (selectedPoints P s) (tracePointSpace C P Finset.univ) ⊓
        (vectorEvaluation moved).ker =
      fixedSpace (regroupedFullPoints off P s moved) noPoints
        (tracePointSpace C P (Finset.univ \ s)) := by
  classical
  ext f
  constructor
  · rintro ⟨hfixed, hmoved⟩
    refine ⟨⟨hfixed.1.1, ?_⟩, ?_, ?_⟩
    · intro i hi
      exact hfixed.1.2 i (Finset.mem_univ i)
    · intro i
      rcases i with i | i
      · exact hfixed.2.1 i
      · rcases i with i | i
        · exact hfixed.2.2 i
        · exact hmoved
    · intro i
      exact i.elim
  · intro hfixed
    have hall : trace K (n + 1) (d + 1) f ∈ tracePointSpace C P Finset.univ := by
      refine ⟨hfixed.1.1, ?_⟩
      intro i _
      by_cases hi : i ∈ s
      · exact trace_evaluation_zero_of_selected_zero P s ⟨i, hi⟩ f
          (hfixed.2.1 (Sum.inr (Sum.inl ⟨i, hi⟩)))
      · exact hfixed.1.2 i (by simp [hi])
    refine ⟨⟨hall, ?_, ?_⟩, ?_⟩
    · intro i
      exact hfixed.2.1 (Sum.inl i)
    · intro i
      exact hfixed.2.1 (Sum.inr (Sum.inl i))
    · exact hfixed.2.1 (Sum.inr (Sum.inr ()))

/-- The regrouped full-point list has precisely one new moving point. -/
theorem regroupedFullPoints_card {p : ℕ} {O : Type*} [Fintype O]
    (s : Finset (Fin p)) :
    Fintype.card (O ⊕ (s ⊕ Unit)) = Fintype.card O + s.card + 1 := by
  simp [Nat.add_assoc]

/-- The complementary trace list has the expected number of points. -/
theorem unselectedTrace_card {p : ℕ} (s : Finset (Fin p)) :
    Fintype.card (↥(Finset.univ \ s)) = p - s.card := by
  rw [Fintype.card_coe, Finset.card_sdiff]
  simp

end IdealGeneration.FractionalRegroup
