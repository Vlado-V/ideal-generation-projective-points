module

public import IdealGeneration.Response
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Choosing the two families of response directions

A spanning family can extend any finite independent list up to the ambient
dimension. Applying this first to one spanning family and then to the other
provides the mixed source directions required in Lemma 4.4.
-/

namespace IdealGeneration

open Module

variable {𝕜 U ι κ : Type*} [Field 𝕜]
  [AddCommGroup U] [Module 𝕜 U]

/-- A spanning family contains a vector outside the span of an independent list
whose length is strictly smaller than the ambient dimension. -/
theorem exists_outside_span_of_spanning
    (v : ι → U) (hv : Submodule.span 𝕜 (Set.range v) = ⊤)
    {r : ℕ} (a : Fin r → U) (ha : LinearIndependent 𝕜 a)
    (hr : r < Module.finrank 𝕜 U) :
    ∃ i, v i ∉ Submodule.span 𝕜 (Set.range a) := by
  classical
  by_contra! h
  have htop : Submodule.span 𝕜 (Set.range a) = ⊤ := by
    apply top_unique
    rw [← hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  have hdim := finrank_span_eq_card ha
  rw [htop, finrank_top, Fintype.card_fin] at hdim
  omega

/-- Extend a given independent list using only members of a fixed spanning family. -/
theorem exists_independent_append_of_spanning
    (v : ι → U) (hv : Submodule.span 𝕜 (Set.range v) = ⊤)
    {r : ℕ} (a : Fin r → U) (ha : LinearIndependent 𝕜 a)
    (s : ℕ) (hrs : r + s ≤ Module.finrank 𝕜 U) :
    ∃ b : Fin s → ι, LinearIndependent 𝕜 (Fin.append a (v ∘ b)) := by
  classical
  induction s with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    simpa only [Fin.append_right_nil _ _ rfl, Nat.add_zero, Fin.cast_refl,
      Function.comp_def, id_eq] using ha
  | succ s ih =>
    obtain ⟨b, hb⟩ := ih (by omega)
    obtain ⟨i, hi⟩ := exists_outside_span_of_spanning v hv
      (Fin.append a (v ∘ b)) hb (by omega)
    refine ⟨Fin.snoc b i, ?_⟩
    rw [Fin.comp_snoc, Fin.append_snoc]
    exact hb.finSnoc hi

/-- A spanning family contains an independent list of every admissible length. -/
theorem exists_independent_list_of_spanning
    (v : ι → U) (hv : Submodule.span 𝕜 (Set.range v) = ⊤)
    (r : ℕ) (hr : r ≤ Module.finrank 𝕜 U) :
    ∃ a : Fin r → ι, LinearIndependent 𝕜 (v ∘ a) := by
  obtain ⟨a, ha⟩ := exists_independent_append_of_spanning v hv
    (Fin.elim0 : Fin 0 → U) (linearIndependent_empty_type) r (by simpa using hr)
  refine ⟨a, ?_⟩
  apply (linearIndependent_equiv (finCongr (Nat.zero_add r))).mp
  simpa only [Fin.elim0_append, Function.comp_def, finCongr_apply] using ha

/-- Select prescribed numbers of directions from two spanning families, with the
combined family linearly independent. -/
theorem exists_mixed_independent_selection
    (α : ι → U) (β : κ → U)
    (hα : Submodule.span 𝕜 (Set.range α) = ⊤)
    (hβ : Submodule.span 𝕜 (Set.range β) = ⊤)
    (a b : ℕ) (hab : a + b ≤ Module.finrank 𝕜 U) :
    ∃ (f : Fin a ↪ ι) (g : Fin b ↪ κ),
      LinearIndependent 𝕜 (Sum.elim (α ∘ f) (β ∘ g)) := by
  classical
  obtain ⟨f, hf⟩ := exists_independent_list_of_spanning α hα a (by omega)
  obtain ⟨g, hfg⟩ := exists_independent_append_of_spanning β hβ (α ∘ f) hf b hab
  have hinj := (Fin.append_injective_iff.mp hfg.injective)
  have hfi : Function.Injective f := fun i j hij => hinj.1 (congrArg α hij)
  have hgi : Function.Injective g := fun i j hij => hinj.2.1 (congrArg β hij)
  refine ⟨⟨f, hfi⟩, ⟨g, hgi⟩, ?_⟩
  change LinearIndependent 𝕜 (Sum.elim (α ∘ f) (β ∘ g))
  have h := hfg.comp finSumFinEquiv finSumFinEquiv.injective
  simpa only [finSumFinEquiv, Equiv.coe_fn_mk, Fin.append_comp_sumElim] using h

/-- The two spanning source families and the uniform independence of target
coordinates supply a response of maximal possible rank. -/
theorem exists_maximal_two_summand_response
    {V A B : Type*}
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    [AddCommGroup A] [Module 𝕜 A] [FiniteDimensional 𝕜 A]
    [AddCommGroup B] [Module 𝕜 B] [FiniteDimensional 𝕜 B]
    (α : ι → Module.Dual 𝕜 V) (β : κ → Module.Dual 𝕜 V)
    (eA : ι → A) (eB : κ → B)
    (hα : Submodule.span 𝕜 (Set.range α) = ⊤)
    (hβ : Submodule.span 𝕜 (Set.range β) = ⊤)
    (heA : ∀ (r : ℕ) (f : Fin r ↪ ι), r ≤ Module.finrank 𝕜 A →
      LinearIndependent 𝕜 (eA ∘ f))
    (heB : ∀ (r : ℕ) (g : Fin r ↪ κ), r ≤ Module.finrank 𝕜 B →
      LinearIndependent 𝕜 (eB ∘ g)) :
    ∃ (a b : ℕ) (f : Fin a ↪ ι) (g : Fin b ↪ κ),
      Module.finrank 𝕜 (LinearMap.range (firstResponse
        (Sum.elim (α ∘ f) (β ∘ g))
        (Sum.elim (LinearMap.inl 𝕜 A B ∘ (eA ∘ f))
          (LinearMap.inr 𝕜 A B ∘ (eB ∘ g))))) =
        min (Module.finrank 𝕜 V) (Module.finrank 𝕜 A + Module.finrank 𝕜 B) := by
  let h := min (Module.finrank 𝕜 V) (Module.finrank 𝕜 A + Module.finrank 𝕜 B)
  let a := min h (Module.finrank 𝕜 A)
  let b := h - a
  have ha : a ≤ Module.finrank 𝕜 A := Nat.min_le_right _ _
  have hh : h ≤ Module.finrank 𝕜 V := Nat.min_le_left _ _
  have hab : a + b = h := by dsimp [a, b]; omega
  have hb : b ≤ Module.finrank 𝕜 B := by dsimp [a, b, h]; omega
  have hdim : a + b ≤ Module.finrank 𝕜 (Module.Dual 𝕜 V) := by
    rw [Subspace.dual_finrank_eq, hab]
    exact hh
  obtain ⟨f, g, hfg⟩ := exists_mixed_independent_selection α β hα hβ a b hdim
  refine ⟨a, b, f, g, ?_⟩
  rw [firstResponse_two_summands_finrank _ _ _ hfg (heA a f ha) (heB b g hb)]
  simpa only [Fintype.card_fin] using hab

/-- Zero-one coefficients selecting the image of an embedding. -/
noncomputable def selectionWeight (𝕜 : Type*) [Field 𝕜] {r : ℕ}
    (f : Fin r ↪ ι) (i : ι) : 𝕜 := by
  classical
  exact if i ∈ Set.range f then 1 else 0

theorem selectionWeight_binary {r : ℕ} (f : Fin r ↪ ι) (i : ι) :
    selectionWeight 𝕜 f i = 0 ∨ selectionWeight 𝕜 f i = 1 := by
  classical
  by_cases hi : i ∈ Set.range f <;> simp [selectionWeight, hi]

/-- A sum with these zero-one coefficients is the sum over the selected indices. -/
theorem sum_selectionWeight
    [Fintype ι] {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    {r : ℕ} (f : Fin r ↪ ι) (v : ι → W) :
    (∑ i, selectionWeight 𝕜 f i • v i) = ∑ j, v (f j) := by
  classical
  symm
  apply Fintype.sum_of_injective f f.injective
  · intro i hi
    simp [selectionWeight, hi]
  · intro j
    simp [selectionWeight]

/-- Weighting the target vectors selects precisely the indicated rank-one maps. -/
theorem firstResponse_selectionWeight
    [Fintype ι] {V W : Type*}
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    {r : ℕ} (f : Fin r ↪ ι) (α : ι → Module.Dual 𝕜 V) (v : ι → W) :
    firstResponse α (fun i => selectionWeight 𝕜 f i • v i) =
      firstResponse (α ∘ f) (v ∘ f) := by
  ext x
  simp only [firstResponse_apply, Function.comp_apply]
  calc
    (∑ i, α i x • (selectionWeight 𝕜 f i • v i)) =
        ∑ i, selectionWeight 𝕜 f i • (α i x • v i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact smul_comm _ _ _
    _ = ∑ j, α (f j) x • v (f j) := sum_selectionWeight f _

/-- Separate target summands separate the two response sums. -/
theorem firstResponse_two_summands_eq_prod
    [Fintype ι] [Fintype κ] {V A B : Type*}
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup A] [Module 𝕜 A] [AddCommGroup B] [Module 𝕜 B]
    (α : ι → Module.Dual 𝕜 V) (β : κ → Module.Dual 𝕜 V)
    (a : ι → A) (b : κ → B) :
    firstResponse (Sum.elim α β)
      (Sum.elim (LinearMap.inl 𝕜 A B ∘ a) (LinearMap.inr 𝕜 A B ∘ b)) =
        (firstResponse α a).prod (firstResponse β b) := by
  ext x <;> simp [firstResponse_apply, Fintype.sum_sum_type, Prod.fst_sum, Prod.snd_sum]

/-- Lemma 4.4's response can be obtained by assigning only zero-one velocities
in the two finite families. This is its complete linear-algebra conclusion. -/
theorem exists_binary_maximal_response
    [Fintype ι] [Fintype κ] {V A B : Type*}
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    [AddCommGroup A] [Module 𝕜 A] [FiniteDimensional 𝕜 A]
    [AddCommGroup B] [Module 𝕜 B] [FiniteDimensional 𝕜 B]
    (α : ι → Module.Dual 𝕜 V) (β : κ → Module.Dual 𝕜 V)
    (eA : ι → A) (eB : κ → B)
    (hα : Submodule.span 𝕜 (Set.range α) = ⊤)
    (hβ : Submodule.span 𝕜 (Set.range β) = ⊤)
    (heA : ∀ (r : ℕ) (f : Fin r ↪ ι), r ≤ Module.finrank 𝕜 A →
      LinearIndependent 𝕜 (eA ∘ f))
    (heB : ∀ (r : ℕ) (g : Fin r ↪ κ), r ≤ Module.finrank 𝕜 B →
      LinearIndependent 𝕜 (eB ∘ g)) :
    ∃ (u : ι → 𝕜) (v : κ → 𝕜),
      (∀ i, u i = 0 ∨ u i = 1) ∧ (∀ j, v j = 0 ∨ v j = 1) ∧
      Module.finrank 𝕜 (LinearMap.range
        ((firstResponse α (fun i => u i • eA i)).prod
          (firstResponse β (fun j => v j • eB j)))) =
        min (Module.finrank 𝕜 V) (Module.finrank 𝕜 A + Module.finrank 𝕜 B) := by
  obtain ⟨a, b, f, g, h⟩ :=
    exists_maximal_two_summand_response α β eA eB hα hβ heA heB
  refine ⟨selectionWeight 𝕜 f, selectionWeight 𝕜 g,
    selectionWeight_binary f, selectionWeight_binary g, ?_⟩
  rw [firstResponse_selectionWeight, firstResponse_selectionWeight]
  rw [firstResponse_two_summands_eq_prod] at h
  exact h

end IdealGeneration
