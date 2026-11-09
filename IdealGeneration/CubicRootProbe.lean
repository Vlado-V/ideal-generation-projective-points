module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finsupp.Order

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Mixed derivative evaluations for the two extended variables in Appendix B.11. -/

namespace IdealGeneration.CubicExtended

open MvPolynomial

def normalIndex (c : Fin 2) : Fin 14 := c.castAdd 12

def oldTraceIndex (j : Fin 10) : Fin 14 := (j.castAdd 2).natAdd 2

def newTraceIndex (w : Fin 2) : Fin 14 := (w.natAdd 10).natAdd 2

private theorem normalIndex_def (c : Fin 2) : normalIndex c = c.castAdd 12 := rfl

private theorem oldTraceIndex_def (j : Fin 10) :
    oldTraceIndex j = (j.castAdd 2).natAdd 2 := rfl

private theorem newTraceIndex_def (w : Fin 2) :
    newTraceIndex w = (w.natAdd 10).natAdd 2 := rfl

private theorem normalIndex_injective : Function.Injective normalIndex := by
  intro c d h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

private theorem newTraceIndex_injective : Function.Injective newTraceIndex := by
  intro w u h
  have hval := congrArg Fin.val h
  simp only [newTraceIndex, Fin.val_natAdd] at hval
  exact Fin.ext (by omega)

private theorem normal_ne_old (c : Fin 2) (j : Fin 10) :
    normalIndex c ≠ oldTraceIndex j := by
  intro h
  have hval := congrArg Fin.val h
  have hc := c.isLt
  simp only [normalIndex, oldTraceIndex, Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

private theorem normal_ne_new (c w : Fin 2) : normalIndex c ≠ newTraceIndex w := by
  intro h
  have hval := congrArg Fin.val h
  have hc := c.isLt
  simp only [normalIndex, newTraceIndex, Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

private theorem new_ne_old (w : Fin 2) (j : Fin 10) :
    newTraceIndex w ≠ oldTraceIndex j := by
  intro h
  have hval := congrArg Fin.val h
  have hj := j.isLt
  simp only [newTraceIndex, oldTraceIndex, Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluate only the ten old trace coordinates, setting the other four to zero. -/
def probePoint (x : Fin 10 → R) : Fin 14 → R :=
  fun i => Fin.addCases (motive := fun _ : Fin (2 + 12) => R)
    (fun _ : Fin 2 => 0)
    (fun j : Fin 12 => Fin.addCases (motive := fun _ : Fin (10 + 2) => R)
      x (fun _ : Fin 2 => 0) j) i

@[simp] theorem probePoint_normal (x : Fin 10 → R) (c : Fin 2) :
    probePoint x (normalIndex c) = 0 := by
  simp [probePoint, normalIndex]

@[simp] theorem probePoint_old (x : Fin 10 → R) (j : Fin 10) :
    probePoint x (oldTraceIndex j) = x j := by
  simp [probePoint, oldTraceIndex]

@[simp] theorem probePoint_new (x : Fin 10 → R) (w : Fin 2) :
    probePoint x (newTraceIndex w) = 0 := by
  simp [probePoint, newTraceIndex]

/-- The coefficient of the chosen normal and new variables, evaluated on an old trace point. -/
noncomputable def rootProbe (x : Fin 10 → R) (c w : Fin 2) :
    MvPolynomial (Fin 14) R →ₗ[R] R :=
  (aeval (probePoint x)).toLinearMap.comp
    ((pderiv (newTraceIndex w)).toLinearMap.comp (pderiv (normalIndex c)).toLinearMap)

theorem rootProbe_apply (x : Fin 10 → R) (c w : Fin 2) (f : MvPolynomial (Fin 14) R) :
    rootProbe x c w f =
      eval (probePoint x) (pderiv (newTraceIndex w) (pderiv (normalIndex c) f)) := by
  simp only [rootProbe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    aeval_eq_eval]
  rfl

/-- The differentiated monomial survives setting the normal and new coordinates to zero. -/
def probeKeeps (c w : Fin 2) (e : Fin 14 →₀ ℕ) : Prop :=
  (∀ d, e (normalIndex d) = if c = d then 1 else 0) ∧
  (∀ u, e (newTraceIndex u) = if w = u then 1 else 0)

instance (c w : Fin 2) (e : Fin 14 →₀ ℕ) : Decidable (probeKeeps c w e) := by
  unfold probeKeeps
  infer_instance

private theorem zeroDerivativeFactors (f : Fin 2 → ℕ) (i : Fin 2) (hi : f i ≠ 0) :
    (∏ j : Fin 2, (0 : R) ^ (f j - if i = j then 1 else 0)) =
      if ∀ j, f j = (if i = j then 1 else 0) then 1 else 0 := by
  split_ifs with h
  · simp [h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have hpos : f j - (if i = j then 1 else 0) ≠ 0 := by
      by_cases hji : i = j
      · subst j
        simp only [↓reduceIte] at hj ⊢
        omega
      · simpa [hji] using hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (zero_pow hpos)

/-- A root probe retains exactly one selected normal and one selected new variable. -/
theorem rootProbe_monomial (x : Fin 10 → R) (c w : Fin 2) (e : Fin 14 →₀ ℕ) (a : R) :
    rootProbe x c w (monomial e a) =
      if probeKeeps c w e then a * ∏ j : Fin 10, x j ^ e (oldTraceIndex j) else 0 := by
  rw [rootProbe_apply, pderiv_monomial, pderiv_monomial, eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_add (a := 2) (b := 12), Fin.prod_univ_add (a := 10) (b := 2)]
  simp only [← normalIndex_def, ← oldTraceIndex_def, ← newTraceIndex_def,
    probePoint_normal, probePoint_old, probePoint_new, Finsupp.tsub_apply, Finsupp.single_apply,
    normalIndex_injective.eq_iff, newTraceIndex_injective.eq_iff,
    normal_ne_old, normal_ne_new, new_ne_old, Ne.symm (normal_ne_new _ _),
    ite_false, Nat.sub_zero]
  by_cases hc : e (normalIndex c) = 0
  · have h : ¬ probeKeeps c w e := fun h => by simpa [hc] using h.1 c
    simp [hc, h]
  by_cases hw : e (newTraceIndex w) = 0
  · have h : ¬ probeKeeps c w e := fun h => by simpa [hw] using h.2 w
    simp [hw, h]
  rw [zeroDerivativeFactors _ _ hc, zeroDerivativeFactors _ _ hw]
  by_cases h : probeKeeps c w e
  · simp [h, h.1, h.2]
  · by_cases hnormal : ∀ d, e (normalIndex d) = if c = d then 1 else 0
    · have hnew : ¬ ∀ u, e (newTraceIndex u) = if w = u then 1 else 0 :=
        fun hnew => h ⟨hnormal, hnew⟩
      simp [h, hnew]
    · simp [h, hnormal]

/-- Mixed derivative evaluation commutes with coefficient specialization. -/
theorem rootProbe_map (g : R →+* S) (x : Fin 10 → R) (c w : Fin 2)
    (f : MvPolynomial (Fin 14) R) :
    g (rootProbe x c w f) = rootProbe (g ∘ x) c w (MvPolynomial.map g f) := by
  have hpoint : g ∘ probePoint x = probePoint (g ∘ x) := by
    funext i
    refine Fin.addCases (motive := fun i : Fin (2 + 12) =>
      (g ∘ probePoint x) i = probePoint (g ∘ x) i) ?_ ?_ i
    · intro j
      simp [Function.comp_apply, ← normalIndex_def]
    · intro j
      refine Fin.addCases (motive := fun j : Fin (10 + 2) =>
        (g ∘ probePoint x) (j.natAdd 2) = probePoint (g ∘ x) (j.natAdd 2)) ?_ ?_ j
      · intro k
        simp [Function.comp_apply, ← oldTraceIndex_def]
      · intro k
        simp [Function.comp_apply, ← newTraceIndex_def]
  rw [rootProbe_apply, rootProbe_apply, pderiv_map, pderiv_map, map_eval, hpoint]

end IdealGeneration.CubicExtended
