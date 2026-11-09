module

public import IdealGeneration.CubicExtendedCert.Checks000
public import IdealGeneration.CubicExtendedCert.Checks021
public import IdealGeneration.CubicExtendedCert.Checks042
public import IdealGeneration.CubicExtendedCert.Checks063
public import IdealGeneration.CubicExtendedCert.Checks084
public import IdealGeneration.CubicExtendedCert.Checks105
public import IdealGeneration.CubicExtendedCert.Checks126
public import Mathlib.Data.List.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

namespace IdealGeneration.CubicExtended

open CertifiedRank Matrix

private theorem forall_fin_of_rows {n : Nat} [NeZero n] {P : Fin n → Prop}
    (h : List.Forall (fun j => P (Fin.ofNat n j)) (List.range n)) : ∀ i, P i := by
  intro i
  have hi : Fin.ofNat n i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  exact hi ▸ (List.forall_iff_forall_mem.mp h i.val (List.mem_range.mpr i.isLt))

private theorem evaluation_rows : ∀ i : Fin 147, EvaluationRowAgrees i := by
  refine forall_fin_of_rows (n := 147) ?_
  exact ⟨
    evaluationRow000, evaluationRow001, evaluationRow002, evaluationRow003, evaluationRow004, evaluationRow005, evaluationRow006, evaluationRow007,
    evaluationRow008, evaluationRow009, evaluationRow010, evaluationRow011, evaluationRow012, evaluationRow013, evaluationRow014, evaluationRow015,
    evaluationRow016, evaluationRow017, evaluationRow018, evaluationRow019, evaluationRow020, evaluationRow021, evaluationRow022, evaluationRow023,
    evaluationRow024, evaluationRow025, evaluationRow026, evaluationRow027, evaluationRow028, evaluationRow029, evaluationRow030, evaluationRow031,
    evaluationRow032, evaluationRow033, evaluationRow034, evaluationRow035, evaluationRow036, evaluationRow037, evaluationRow038, evaluationRow039,
    evaluationRow040, evaluationRow041, evaluationRow042, evaluationRow043, evaluationRow044, evaluationRow045, evaluationRow046, evaluationRow047,
    evaluationRow048, evaluationRow049, evaluationRow050, evaluationRow051, evaluationRow052, evaluationRow053, evaluationRow054, evaluationRow055,
    evaluationRow056, evaluationRow057, evaluationRow058, evaluationRow059, evaluationRow060, evaluationRow061, evaluationRow062, evaluationRow063,
    evaluationRow064, evaluationRow065, evaluationRow066, evaluationRow067, evaluationRow068, evaluationRow069, evaluationRow070, evaluationRow071,
    evaluationRow072, evaluationRow073, evaluationRow074, evaluationRow075, evaluationRow076, evaluationRow077, evaluationRow078, evaluationRow079,
    evaluationRow080, evaluationRow081, evaluationRow082, evaluationRow083, evaluationRow084, evaluationRow085, evaluationRow086, evaluationRow087,
    evaluationRow088, evaluationRow089, evaluationRow090, evaluationRow091, evaluationRow092, evaluationRow093, evaluationRow094, evaluationRow095,
    evaluationRow096, evaluationRow097, evaluationRow098, evaluationRow099, evaluationRow100, evaluationRow101, evaluationRow102, evaluationRow103,
    evaluationRow104, evaluationRow105, evaluationRow106, evaluationRow107, evaluationRow108, evaluationRow109, evaluationRow110, evaluationRow111,
    evaluationRow112, evaluationRow113, evaluationRow114, evaluationRow115, evaluationRow116, evaluationRow117, evaluationRow118, evaluationRow119,
    evaluationRow120, evaluationRow121, evaluationRow122, evaluationRow123, evaluationRow124, evaluationRow125, evaluationRow126, evaluationRow127,
    evaluationRow128, evaluationRow129, evaluationRow130, evaluationRow131, evaluationRow132, evaluationRow133, evaluationRow134, evaluationRow135,
    evaluationRow136, evaluationRow137, evaluationRow138, evaluationRow139, evaluationRow140, evaluationRow141, evaluationRow142, evaluationRow143,
    evaluationRow144, evaluationRow145, evaluationRow146
  ⟩

private theorem rowValue_filtered {n : ℕ} (f : Fin n → ℕ) (j : Fin n) :
    rowValue ((List.ofFn fun i => (i, f i)).filter (fun e => e.2 != 0)) j = f j := by
  have h (l : List (Fin n × ℕ)) :
      rowValue (l.filter fun e => e.2 != 0) j = rowValue l j := by
    induction l with
    | nil => rfl
    | cons e l ih =>
      simp only [rowValue] at ih
      by_cases he : e.2 = 0 <;> simp [he, rowValue, ih]
  rw [h, rowValue, List.map_ofFn, List.sum_ofFn]
  simp

/-- The listed `E′P` equals the actual monomial evaluation matrix modulo1009. -/
theorem listedEPPrime_eq_actual : listedEPPrime = normalEvaluationMatrix (ZMod 1009) := by
  ext i j
  calc
    listedEPPrime i j = ((rowValue (computedRow i) j : Nat) : ZMod 1009) :=
      congrArg (fun row => ((rowValue row j : Nat) : ZMod 1009))
        (evaluation_rows i).row_eq.symm
    _ = (residueEntry i j : ZMod 1009) :=
      congrArg (fun value : Nat => (value : ZMod 1009)) (rowValue_filtered (residueEntry i) j)
    _ = normalEvaluationMatrix (ZMod 1009) i j :=
      CubicInitial.cast_residueEvaluationEntry (pointCoordinate i) (normalCode j)

#print axioms listedEPPrime_eq_actual

end IdealGeneration.CubicExtended
