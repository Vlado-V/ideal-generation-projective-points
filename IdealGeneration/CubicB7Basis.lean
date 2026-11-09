module

public import IdealGeneration.CubicParameterExtensionBasis
public import IdealGeneration.CubicB11Actual

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The lower and higher B.4 columns as scalar coordinates of the enlarged source. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Compatible

open Parameters

variable {K : Type*} [Field K] {m : ℕ}
variable {P : Parameters K m} {Q : Parameters K (m + 2)} (h : Compatible P Q)

private theorem newVertex_ne_old (b : Fin 2) (i : Fin m) :
    Fin.natAdd m b ≠ Fin.castAdd 2 i := by
  intro hi
  have he := congrArg Fin.val hi
  change m + b.val = i.val at he
  omega

private def localIncidence (hQ : ∀ e, Q.single e = B5.single e)
    (b : Fin 2) (i : {i : Fin m // B5.neighbor b i}) : NewIncidence Q :=
  ⟨(i.val, b), (hQ _).trans ((B5.single_eq_true _).mpr i.property)⟩

/-- The five lower-column labels in the unadjusted scalar basis. -/
def lowerIndex (hP : ∀ e, P.single e = B5.single e)
    (hQ : ∀ e, Q.single e = B5.single e) : B5.B7Column m → Q.ParameterIndex
  | .localColumn b (.inl e) => .edgeTensor (Fin.natAdd m b)
      (h.singleEdge ⟨e.val, (hP e.val).trans e.property⟩)
  | .localColumn b (.inr i) => .edgeTensor (Fin.castAdd 2 i.2)
      (crossSingleEdge Q (localIncidence hQ b i.1))
  | .motion b i q => .antisymmetric (crossEdge i b) q
  | .extra b i u => .normalEdge u (crossSingleEdge Q (localIncidence hQ b i))
  | .remaining b u q => .mixed u (Fin.natAdd m b) q

/-- The higher-column labels, two per incidence and three for the new pair. -/
abbrev HigherIndex := (NewIncidence Q × Fin 2) ⊕ Fin 3

/-- The higher-column labels in the unadjusted scalar basis. -/
def higherIndex : HigherIndex (Q := Q) → Q.ParameterIndex
  | .inl (p, b) => .edgeTensor (Fin.natAdd m b) (crossSingleEdge Q p)
  | .inr q => .antisymmetric (newPairEdge m) q

@[local simp] private theorem oldIndex_pure (q : Fin 3) :
    h.oldParameterIndex (.pure q) = .pure q := rfl

@[local simp] private theorem oldIndex_mixed (u : Fin 2) (i : Fin m) (q : Fin 3) :
    h.oldParameterIndex (.mixed u i q) = .mixed u (Fin.castAdd 2 i) q := rfl

@[local simp] private theorem oldIndex_normalEdge (u : Fin 2) (e : P.SingleEdge) :
    h.oldParameterIndex (.normalEdge u e) = .normalEdge u (h.singleEdge e) := rfl

@[local simp] private theorem oldIndex_antisymmetric (e : Edge m) (q : Fin 3) :
    h.oldParameterIndex (.antisymmetric e q) = .antisymmetric (oldEdge m e) q := rfl

@[local simp] private theorem oldIndex_edgeTensor (i : Fin m) (e : P.SingleEdge) :
    h.oldParameterIndex (.edgeTensor i e) = .edgeTensor (Fin.castAdd 2 i) (h.singleEdge e) := rfl

private theorem newParameter_mixed (u b : Fin 2) (q : Fin 3) :
    ParameterIndex.mixed u (Fin.natAdd m b) q ∉ Set.range h.oldParameterIndex := by
  rintro ⟨i, hi⟩
  cases i <;> simp at hi
  exact newVertex_ne_old _ _ hi.2.1.symm

private theorem newParameter_normalEdge (u : Fin 2) (p : NewIncidence Q) :
    ParameterIndex.normalEdge u (crossSingleEdge Q p) ∉ Set.range h.oldParameterIndex := by
  rintro ⟨i, hi⟩
  cases i <;> simp at hi
  exact h.crossSingleEdge_not_old p ⟨_, hi.2⟩

private theorem newParameter_antisymmetric (a : Edge (m + 2)) (q : Fin 3)
    (ha : a ∉ Set.range (oldEdge m)) :
    ParameterIndex.antisymmetric a q ∉ Set.range h.oldParameterIndex := by
  rintro ⟨i, hi⟩
  cases i <;> simp at hi
  exact ha ⟨_, hi.1⟩

private theorem newParameter_edgeTensor (i : Fin (m + 2)) (a : Q.SingleEdge)
    (ha : (∀ j : Fin m, i ≠ Fin.castAdd 2 j) ∨ a ∉ Set.range h.singleEdge) :
    ParameterIndex.edgeTensor i a ∉ Set.range h.oldParameterIndex := by
  rintro ⟨j, hj⟩
  cases j <;> simp at hj
  rcases ha with hv | he
  · exact hv _ hj.1.symm
  · exact he ⟨_, hj.2⟩

/-- Each lower column belongs to the new scalar source. -/
def lowerNewIndex (hP : ∀ e, P.single e = B5.single e)
    (hQ : ∀ e, Q.single e = B5.single e) (c : B5.B7Column m) : h.NewParameterIndex := by
  refine ⟨h.lowerIndex hP hQ c, ?_⟩
  cases c with
  | localColumn b c =>
      rcases c with c | ⟨i, j⟩
      · exact h.newParameter_edgeTensor _ _ (.inl (newVertex_ne_old b))
      · exact h.newParameter_edgeTensor _ _ (.inr (h.crossSingleEdge_not_old (localIncidence hQ b i)))
  | motion b i q => exact h.newParameter_antisymmetric _ _ (crossEdge_not_old i b)
  | extra b i u => exact h.newParameter_normalEdge u (localIncidence hQ b i)
  | remaining b u q => exact h.newParameter_mixed u b q

/-- Each higher column belongs to the new scalar source. -/
def higherNewIndex (c : HigherIndex (Q := Q)) : h.NewParameterIndex := by
  refine ⟨higherIndex c, ?_⟩
  rcases c with ⟨p, b⟩ | q
  · exact h.newParameter_edgeTensor _ _ (.inl (newVertex_ne_old b))
  · exact h.newParameter_antisymmetric _ _ (newPairEdge_not_old m)


private theorem oldSingle_ne_cross (e : P.SingleEdge) (p : NewIncidence Q) :
    h.singleEdge e ≠ crossSingleEdge Q p := fun he => h.crossSingleEdge_not_old p ⟨e, he⟩

private theorem crossEdge_ne_pair (i : Fin m) (b : Fin 2) :
    crossEdge i b ≠ newPairEdge m := by
  intro he
  have hh := congrArg (edgeExtensionEquiv m) he
  simp at hh

attribute [local simp] newVertex_ne_old oldSingle_ne_cross crossEdge_ne_pair

variable (hP : ∀ e, P.single e = B5.single e) (hQ : ∀ e, Q.single e = B5.single e)

/-- Include the lower and higher labels in one basis of new coordinates. -/
def newIndexMap : B5.B7Column m ⊕ HigherIndex (Q := Q) → h.NewParameterIndex :=
  Sum.elim (h.lowerNewIndex hP hQ) h.higherNewIndex

@[local simp] private theorem oldVertex_ne_new (i : Fin m) (b : Fin 2) :
    Fin.castAdd 2 i ≠ Fin.natAdd m b := Ne.symm (newVertex_ne_old b i)

@[local simp] private theorem crossSingle_ne_old (p : NewIncidence Q) (e : P.SingleEdge) :
    crossSingleEdge Q p ≠ h.singleEdge e := Ne.symm (h.oldSingle_ne_cross e p)

@[local simp] private theorem pairEdge_ne_cross (i : Fin m) (b : Fin 2) :
    newPairEdge m ≠ crossEdge i b := Ne.symm (crossEdge_ne_pair i b)

set_option maxHeartbeats 1200000 in
private theorem newIndexMap_injective : Function.Injective (h.newIndexMap hP hQ) := by
  rintro (x | x) (y | y) he
  all_goals
    have he' := congrArg (fun i : h.NewParameterIndex => i.val) he
    clear he
  · rcases x with ⟨b, e | ⟨i, j⟩⟩ | ⟨b, i, q⟩ | ⟨b, i, u⟩ | ⟨b, u, q⟩ <;>
      rcases y with ⟨c, e' | ⟨i', j'⟩⟩ | ⟨c, i', q'⟩ | ⟨c, i', u'⟩ | ⟨c, u', q'⟩ <;>
      simp_all [newIndexMap, lowerNewIndex, lowerIndex, localIncidence, Subtype.ext_iff]
    all_goals
      first
      | rcases he' with ⟨hb, he⟩
        subst c
        exact heq_of_eq (congrArg (Sum.inl : _ → B5.LocalColumn m b) (Subtype.ext (Subtype.ext he)))
      | rcases he' with ⟨_, hi, hb⟩
        subst c
        exact heq_of_eq (congrArg (fun z => (Sum.inr (z, j') : B5.LocalColumn m b))
          (Subtype.ext hi))
      | rcases he' with ⟨_, hi, hb⟩
        subst c
        exact heq_of_eq (Subtype.ext hi)
  · rcases x with ⟨b, e | ⟨i, j⟩⟩ | ⟨b, i, q⟩ | ⟨b, i, u⟩ | ⟨b, u, q⟩ <;>
      rcases y with ⟨p, c⟩ | q' <;>
      simp_all [newIndexMap, lowerNewIndex, higherNewIndex, lowerIndex, higherIndex]
  · rcases x with ⟨p, b⟩ | q <;>
      rcases y with ⟨c, e' | ⟨i', j'⟩⟩ | ⟨c, i', q'⟩ | ⟨c, i', u'⟩ | ⟨c, u', q'⟩ <;>
      simp_all [newIndexMap, lowerNewIndex, higherNewIndex, lowerIndex, higherIndex]
  · rcases x with ⟨p, b⟩ | q <;> rcases y with ⟨r, c⟩ | q' <;>
      simp_all [newIndexMap, higherNewIndex, higherIndex]

private theorem newIndexMap_surjective (hpair : Q.single (newPairEdge m) = false) :
    Function.Surjective (h.newIndexMap hP hQ) := by
  rintro ⟨i, hi⟩
  have identifyIncidence (p : NewIncidence Q) : B5.neighbor p.val.2 p.val.1 :=
    (B5.single_eq_true _).mp ((hQ _).symm.trans p.property)
  cases i with
  | pure q =>
      exact False.elim (hi ⟨.pure q, rfl⟩)
  | mixed u i q =>
      revert hi
      refine Fin.addCases (fun j hj => ?_) (fun b _ => ?_) i
      · exact False.elim (hj ⟨.mixed u j q, rfl⟩)
      · exact ⟨.inl (.remaining b u q), Subtype.ext rfl⟩
  | normalEdge u a =>
      obtain ⟨j, rfl⟩ := (h.singleEdgeExtensionEquiv hpair).symm.surjective a
      rcases j with e | p
      · exact False.elim (hi ⟨.normalEdge u e, rfl⟩)
      · exact ⟨.inl (.extra p.val.2 ⟨p.val.1, identifyIncidence p⟩ u), Subtype.ext rfl⟩
  | antisymmetric a q =>
      obtain ⟨j, rfl⟩ := (edgeExtensionEquiv m).symm.surjective a
      rcases j with e | (⟨i, b⟩ | ⟨⟩)
      · exact False.elim (hi ⟨.antisymmetric e q, rfl⟩)
      · exact ⟨.inl (.motion b i q), Subtype.ext rfl⟩
      · exact ⟨.inr (.inr q), Subtype.ext rfl⟩
  | edgeTensor i a =>
      obtain ⟨j, rfl⟩ := (h.singleEdgeExtensionEquiv hpair).symm.surjective a
      revert hi
      refine Fin.addCases (fun i hi => ?_) (fun b _ => ?_) i
      · rcases j with e | p
        · exact False.elim (hi ⟨.edgeTensor i e, rfl⟩)
        · exact ⟨.inl (.localColumn p.val.2 (.inr (⟨p.val.1, identifyIncidence p⟩, i))),
            Subtype.ext rfl⟩
      · rcases j with e | p
        · exact ⟨.inl (.localColumn b (.inl ⟨e.val, (hP _).symm.trans e.property⟩)),
            Subtype.ext rfl⟩
        · exact ⟨.inr (.inl (p, b)), Subtype.ext rfl⟩

/-- The five lower and two higher families exhaust the unadjusted new basis. -/
def newIndexEquiv (hpair : Q.single (newPairEdge m) = false) :
    (B5.B7Column m ⊕ HigherIndex (Q := Q)) ≃ h.NewParameterIndex :=
  Equiv.ofBijective (h.newIndexMap hP hQ)
    ⟨h.newIndexMap_injective hP hQ, h.newIndexMap_surjective hP hQ hpair⟩

end IdealGeneration.CubicSupported.Compatible
