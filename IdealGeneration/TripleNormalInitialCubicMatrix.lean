module

public import IdealGeneration.TripleNormalInitialData
public import IdealGeneration.TripleNormalInitialBasisData
public import IdealGeneration.ConeMiddleMatrix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! A computational presentation of the selected cubic coefficient matrix. -/

noncomputable section
namespace IdealGeneration.TripleNormalInitial
open ConeMonomialChart Matrix
set_option maxRecDepth 8192

abbrev NormalIndex := Fin 28 ⊕ Fin 14
abbrev TraceIndex := Fin 52 ⊕ Fin 26
abbrev CubicColumn := MiddleColumn 3 12 (Fin 14) (Fin 26)
abbrev Pair := Fin 15 × Fin 15
abbrev Triple := Fin 15 × Fin 15 × Fin 15

/-- The paper orders the normal and trace columns by basis vector first. -/
def paperColumnOrder : CubicColumn ≃ Fin 288 :=
  (Equiv.sumCongr ((Equiv.prodComm (Fin 15) (Fin 14)).trans finProdFinEquiv)
    ((Equiv.prodComm (Fin 3) (Fin 26)).trans finProdFinEquiv)).trans finSumFinEquiv

def normalPair (i : NormalIndex) : Pair :=
  let t := normalQuadraticTuple (normalColumn i)
  (t.1.castAdd 12, t.2)

def tracePair (i : TraceIndex) : Pair :=
  let t := traceQuadraticTuple (traceColumn i)
  (t.1.natAdd 3, t.2.natAdd 3)

def pairExponent (t : Pair) : Fin 15 →₀ ℕ :=
  Finsupp.single t.1 1 + Finsupp.single t.2 1

def tripleExponent (t : Triple) : Fin 15 →₀ ℕ :=
  Finsupp.single t.1 1 + Finsupp.single t.2.1 1 + Finsupp.single t.2.2 1

private theorem traceExponent_extend (i : TraceIndex) :
    (traceExponent i).mapDomain (Fin.natAdd 3) = pairExponent (tracePair i) := by
  simp only [traceExponent, traceExponentLex, pairExponent, tracePair, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single]

private theorem normalPair_injective : Function.Injective normalPair := by
  intro i j h
  exact normalExponent_injective (congrArg pairExponent h)

private theorem tracePair_injective : Function.Injective tracePair := by
  intro i j h
  apply traceExponent_injective
  apply Finsupp.mapDomain_injective (Fin.natAdd_injective 12 3)
  rw [traceExponent_extend, traceExponent_extend, h]

private theorem normalPair_sorted : ∀ i, (normalPair i).1 ≤ (normalPair i).2 := by
  decide +kernel

private theorem tracePair_sorted : ∀ i, (tracePair i).1 ≤ (tracePair i).2 := by
  decide +kernel

private theorem cubicPivotTuple_sorted : ∀ i,
    (cubicPivotTuple i).1 ≤ (cubicPivotTuple i).2.1 ∧
      (cubicPivotTuple i).2.1 ≤ (cubicPivotTuple i).2.2 := by
  decide +kernel

/-- Removing the multiplier leaves the unique possible source pair. -/
def dropMultiplier (j : Fin 15) (t : Triple) : Option Pair :=
  if j = t.1 then some (t.2.1, t.2.2)
  else if j = t.2.1 then some (t.1, t.2.2)
  else if j = t.2.2 then some (t.1, t.2.1)
  else none

private theorem dropMultiplier_some {j : Fin 15} {t : Triple} {p : Pair}
    (ht : t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2) (h : dropMultiplier j t = some p) :
    p.1 ≤ p.2 ∧ tripleExponent t = Finsupp.single j 1 + pairExponent p := by
  by_cases h₁ : j = t.1
  · rw [dropMultiplier, ite_eq_left h₁, Option.some.injEq] at h
    subst p
    refine ⟨ht.2, ?_⟩
    rw [h₁]
    simp only [tripleExponent, pairExponent]
    abel
  by_cases h₂ : j = t.2.1
  · rw [dropMultiplier, ite_eq_right h₁, ite_eq_left h₂, Option.some.injEq] at h
    subst p
    refine ⟨ht.1.trans ht.2, ?_⟩
    rw [h₂]
    simp only [tripleExponent, pairExponent]
    abel
  by_cases h₃ : j = t.2.2
  · rw [dropMultiplier, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃, Option.some.injEq] at h
    subst p
    refine ⟨ht.1, ?_⟩
    rw [h₃]
    simp only [tripleExponent, pairExponent]
    abel
  simp [dropMultiplier, h₁, h₂, h₃] at h

private theorem dropMultiplier_none {j : Fin 15} {t : Triple}
    (h : dropMultiplier j t = none) : j ≠ t.1 ∧ j ≠ t.2.1 ∧ j ≠ t.2.2 := by
  unfold dropMultiplier at h
  split_ifs at h
  simp_all

private theorem shiftedCoeff_eq_dropMultiplier {R : Type*} [CommSemiring R]
    (j : Fin 15) (t : Triple) (p : Pair) (x : R)
    (ht : t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2) (hp : p.1 ≤ p.2) :
    shiftedCoeff (pairExponent p) (tripleExponent t) j x =
      if dropMultiplier j t = some p then x else 0 := by
  cases hdrop : dropMultiplier j t with
  | none =>
      obtain ⟨h₁, h₂, h₃⟩ := dropMultiplier_none hdrop
      have hne : Finsupp.single j 1 + pairExponent p ≠ tripleExponent t := by
        intro h
        have he := congrArg (fun f : Fin 15 →₀ ℕ => f j) h
        simp only [tripleExponent, Finsupp.add_apply, Finsupp.single_apply, Ne.symm h₁,
          Ne.symm h₂, Ne.symm h₃, ite_false, ite_true, add_zero] at he
        omega
      simp [shiftedCoeff, hne]
  | some u =>
      obtain ⟨hu, he⟩ := dropMultiplier_some ht hdrop
      have hiff : Finsupp.single j 1 + pairExponent p = tripleExponent t ↔ u = p := by
        rw [he]
        constructor
        · intro h
          have hpairs : pairExponent p = pairExponent u := add_left_cancel h
          obtain ⟨h₁, h₂⟩ := sorted_pair_exponents_injective hp hu hpairs
          exact (Prod.ext h₁ h₂).symm
        · rintro rfl
          rfl
      simp only [shiftedCoeff, hiff, Option.some.injEq]

def lookupCoefficient {ι α R : Type*} [DecidableEq α] [Zero R]
    (indices : List ι) (f : ι → α) (b : ι → R) (p : Option α) : R :=
  match p with
  | none => 0
  | some t => (indices.find? (fun i => decide (f i = t))).elim 0 b

private theorem sum_eq_lookupCoefficient {ι α R : Type*} [Fintype ι] [DecidableEq α]
    [AddCommMonoid R] (indices : List ι) (f : ι → α) (b : ι → R) (p : Option α)
    (hindices : ∀ i, i ∈ indices) (hf : Function.Injective f) :
    (∑ i, if p = some (f i) then b i else 0) = lookupCoefficient indices f b p := by
  classical
  cases p with
  | none => simp [lookupCoefficient]
  | some t =>
      simp only [lookupCoefficient, Option.some.injEq]
      cases h : indices.find? (fun i => decide (f i = t)) with
      | none =>
          have hne (i : ι) : t ≠ f i := by
            intro hi
            exact (List.find?_eq_none.mp h i (hindices i)) (by simp [hi])
          simp [hne]
      | some i =>
          have hib : decide (f i = t) = true :=
            List.find?_some (p := fun j : ι => decide (f j = t)) h
          have hi : f i = t := of_decide_eq_true hib
          rw [Finset.sum_eq_single i]
          · simp [hi]
          · intro j _ hji
            have hj : t ≠ f j := fun he => hji (hf (he.symm.trans hi.symm))
            simp [hj]
          · simp

def normalIndices : List NormalIndex :=
  (List.finRange 28).map Sum.inl ++ (List.finRange 14).map Sum.inr

def traceIndices : List TraceIndex :=
  (List.finRange 52).map Sum.inl ++ (List.finRange 26).map Sum.inr

private theorem mem_normalIndices (i : NormalIndex) : i ∈ normalIndices := by
  cases i <;> simp [normalIndices, List.mem_finRange]

private theorem mem_traceIndices (i : TraceIndex) : i ∈ traceIndices := by
  cases i <;> simp [traceIndices, List.mem_finRange]

/-- One table lookup computes the coefficient of a selected cubic in each column. -/
def fastMiddleMod : Matrix (Fin 288) CubicColumn ModField :=
  fun i => Sum.elim
    (fun j => lookupCoefficient normalIndices normalPair (fun a => normalKernelMod a j.2)
      (dropMultiplier j.1 (cubicPivotTuple i)))
    (fun j => lookupCoefficient traceIndices tracePair (fun a => traceKernelMod a j.2)
      (dropMultiplier (j.1.castAdd 12) (cubicPivotTuple i)))

/-- The computational matrix is the actual monomial coefficient matrix. -/
theorem middleMatrix_eq_fastMiddleMod :
    middleMatrix normalExponent traceExponent cubicExponent normalKernelMod traceKernelMod =
      fastMiddleMod := by
  ext i col
  cases col with
  | inl j =>
      change (∑ a, shiftedCoeff (pairExponent (normalPair a)) (tripleExponent (cubicPivotTuple i))
        j.1 (normalKernelMod a j.2)) = _
      simp_rw [shiftedCoeff_eq_dropMultiplier _ _ _ _ (cubicPivotTuple_sorted i) (normalPair_sorted _)]
      exact sum_eq_lookupCoefficient normalIndices normalPair _ _ mem_normalIndices normalPair_injective
  | inr j =>
      change (∑ a, shiftedCoeff ((traceExponent a).mapDomain (Fin.natAdd 3))
        (tripleExponent (cubicPivotTuple i)) (j.1.castAdd 12) (traceKernelMod a j.2)) = _
      simp_rw [traceExponent_extend,
        shiftedCoeff_eq_dropMultiplier _ _ _ _ (cubicPivotTuple_sorted i) (tracePair_sorted _)]
      exact sum_eq_lookupCoefficient traceIndices tracePair _ _ mem_traceIndices tracePair_injective

def orderedMiddleMod : Matrix (Fin 288) (Fin 288) ModField :=
  (middleMatrix normalExponent traceExponent cubicExponent normalKernelMod traceKernelMod).submatrix
    id paperColumnOrder.symm

theorem orderedMiddleMod_eq_fast : orderedMiddleMod = fastMiddleMod.submatrix id paperColumnOrder.symm := by
  rw [orderedMiddleMod, middleMatrix_eq_fastMiddleMod]

end IdealGeneration.TripleNormalInitial
