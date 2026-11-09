module

public import IdealGeneration.ConeMiddleLookup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Coordinate guards certify predecessor lookups in the cone monomial chart. -/

namespace IdealGeneration.ConeMonomialChart

variable {c m : ℕ} {ν τ : Type*}

/-- A normal lookup either records the predecessor or a reason none exists. -/
def NormalLookupValid (en : ν → Fin (c + m) →₀ ℕ)
    (u : Fin (c + m) →₀ ℕ) (j : Fin (c + m)) : Option ν → Prop
  | none => u j = 0 ∨ ∀ l : Fin c, u (l.castAdd m) = if j = l.castAdd m then 1 else 0
  | some a => ∀ k, (if j = k then 1 else 0) + en a k = u k

instance normalLookupValidDecidable
    (en : ν → Fin (c + m) →₀ ℕ) (u : Fin (c + m) →₀ ℕ)
    (j : Fin (c + m)) (look : Option ν) : Decidable (NormalLookupValid en u j look) := by
  cases look <;> simp only [NormalLookupValid] <;> infer_instance

theorem normalLookup_iff_of_valid
    (en : ν → Fin (c + m) →₀ ℕ)
    (he : Function.Injective en) (hn : ∀ a, ∃ l : Fin c, en a (l.castAdd m) ≠ 0)
    (u : Fin (c + m) →₀ ℕ) (j : Fin (c + m)) (look : Option ν)
    (h : NormalLookupValid en u j look) (a : ν) :
    Finsupp.single j 1 + en a = u ↔ look = some a := by
  cases look with
  | none =>
    constructor
    · intro ha
      change u j = 0 ∨ _ at h
      exfalso
      rcases h with h | h
      · have ha' := congrArg (fun e : Fin (c + m) →₀ ℕ => e j) ha
        simp [Finsupp.add_apply, h] at ha'
      · obtain ⟨l, hl⟩ := hn a
        have ha' := congrArg (fun e : Fin (c + m) →₀ ℕ => e (l.castAdd m)) ha
        simp only [Finsupp.add_apply, Finsupp.single_apply, h l] at ha'
        omega
    · simp
  | some a₀ =>
    have ha₀ : Finsupp.single j 1 + en a₀ = u := by
      ext k
      simpa only [Finsupp.add_apply, Finsupp.single_apply] using h k
    rw [← ha₀]
    constructor
    · intro ha
      exact congrArg some ((he (add_left_cancel ha)).symm)
    · intro ha
      rw [Option.some.inj ha]

/-- A trace lookup uses the normal part to rule out a predecessor, or gives
the full trace exponent when the normal part is exactly the chosen variable. -/
def TraceLookupValid (et : τ → Fin m →₀ ℕ)
    (u : Fin (c + m) →₀ ℕ) (j : Fin c) : Option τ → Prop
  | none => ∃ l : Fin c, u (l.castAdd m) ≠ if j = l then 1 else 0
  | some a => (∀ l : Fin c, u (l.castAdd m) = if j = l then 1 else 0) ∧
      ∀ k : Fin m, et a k = u (k.natAdd c)

instance traceLookupValidDecidable
    (et : τ → Fin m →₀ ℕ) (u : Fin (c + m) →₀ ℕ)
    (j : Fin c) (look : Option τ) : Decidable (TraceLookupValid et u j look) := by
  cases look <;> simp only [TraceLookupValid] <;> infer_instance

private theorem castAdd_ne_natAdd (j : Fin c) (k : Fin m) :
    j.castAdd m ≠ k.natAdd c := by
  intro h
  have he := congrArg Fin.val h
  simp at he
  omega

theorem traceLookup_iff_of_valid
    (et : τ → Fin m →₀ ℕ) (he : Function.Injective et)
    (u : Fin (c + m) →₀ ℕ) (j : Fin c) (look : Option τ)
    (h : TraceLookupValid et u j look) (a : τ) :
    Finsupp.single (j.castAdd m) 1 + (et a).mapDomain (Fin.natAdd c) = u ↔
      look = some a := by
  have hnormal (b : τ) (l : Fin c) : ((et b).mapDomain (Fin.natAdd c)) (l.castAdd m) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨k, hk⟩
    exact castAdd_ne_natAdd l k hk.symm
  have hinj : Function.Injective (Fin.natAdd c : Fin m → Fin (c + m)) := Fin.natAdd_injective _ _
  have htail (b : τ) (k : Fin m) : ((et b).mapDomain (Fin.natAdd c)) (k.natAdd c) = et b k :=
    Finsupp.mapDomain_apply_of_injective hinj _ _
  cases look with
  | none =>
    constructor
    · intro ha
      obtain ⟨l, hl⟩ := h
      have ha' := congrArg (fun e : Fin (c + m) →₀ ℕ => e (l.castAdd m)) ha
      simp only [Finsupp.add_apply, Finsupp.single_apply, hnormal, add_zero,
        Fin.castAdd_inj] at ha'
      exact (hl ha'.symm).elim
    · simp
  | some a₀ =>
    have ha₀ : Finsupp.single (j.castAdd m) 1 + (et a₀).mapDomain (Fin.natAdd c) = u := by
      ext k
      refine Fin.addCases (fun l => ?_) (fun l => ?_) k
      · simpa only [Finsupp.add_apply, Finsupp.single_apply, hnormal, add_zero,
          Fin.castAdd_inj] using (h.1 l).symm
      · simpa only [Finsupp.add_apply, Finsupp.single_apply, htail,
          castAdd_ne_natAdd, ite_false, zero_add] using h.2 l
    rw [← ha₀]
    constructor
    · intro ha
      exact congrArg some ((he (Finsupp.mapDomain_injective hinj (add_left_cancel ha))).symm)
    · intro ha
      rw [Option.some.inj ha]

end IdealGeneration.ConeMonomialChart
