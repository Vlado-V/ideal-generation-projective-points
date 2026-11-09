module

public import IdealGeneration.ConeSplitting

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Middle multiplication depends on the point representatives, independent of their labels. -/

noncomputable section
namespace IdealGeneration.ConeConfiguration
open MvPolynomial

variable {K : Type*} [Field K] {c m p q p' q' d : ℕ}

/-- A configuration covering both sets of representatives inherits
injectivity of actual middle multiplication. -/
theorem middle_injective_of_representative_coverage
    (C : ConeConfiguration K c m p q) (D : ConeConfiguration K c m p' q')
    (hp : ∀ i, ∃ j, D.point j = C.point i)
    (hq : ∀ i, ∃ j, D.trace j = C.trace i)
    (hinj : Function.Injective (C.middleMultiplication d)) :
    Function.Injective (D.middleMultiplication d) := by
  let a (f : (Fin (c + m) → D.residualPiece d) × (Fin c → D.tracePiece d)) :
      (Fin (c + m) → C.residualPiece d) × (Fin c → C.tracePiece d) :=
    (fun j => ⟨(f.1 j).val, by
      refine ⟨(C.mem_conePiece _).mpr ?_, (f.1 j).property.2⟩
      intro i
      obtain ⟨l, hl⟩ := hp i
      rw [← hl]
      exact (D.mem_conePiece _).mp (f.1 j).property.1 l⟩,
      fun j => ⟨(f.2 j).val, by
        apply (C.mem_tracePiece _).mpr
        intro i
        obtain ⟨l, hl⟩ := hq i
        rw [← hl]
        exact (D.mem_tracePiece _).mp (f.2 j).property l⟩)
  have ha : Function.Injective a := by
    intro f g h
    apply Prod.ext
    · funext j
      apply Subtype.ext
      exact congrArg (fun z => (z.1 j).val) h
    · funext j
      apply Subtype.ext
      exact congrArg (fun z => (z.2 j).val) h
  have hm (f : (Fin (c + m) → D.residualPiece d) × (Fin c → D.tracePiece d)) :
      (C.middleMultiplication d (a f)).val.val = (D.middleMultiplication d f).val.val := by
    rw [C.middleMultiplication_val, D.middleMultiplication_val]
    have ht : C.normalTraceCoefficients d (a f).2 = D.normalTraceCoefficients d f.2 := by
      funext j
      exact Fin.addCases (motive := fun j => C.normalTraceCoefficients d (a f).2 j =
        D.normalTraceCoefficients d f.2 j)
        (fun i => by simp only [normalTraceCoefficients, Fin.addCases_left]; rfl)
        (fun i => by simp only [normalTraceCoefficients, Fin.addCases_right]) j
    rw [ht]
  intro f g h
  apply ha
  apply hinj
  apply Subtype.ext
  apply Subtype.ext
  rw [hm, hm]
  exact congrArg (fun z => z.val.val) h

end IdealGeneration.ConeConfiguration
