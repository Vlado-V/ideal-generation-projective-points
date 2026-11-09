module

public import IdealGeneration.CubicB7RootInitialAgreement
public import IdealGeneration.CubicB11PoolPatch
public import IdealGeneration.CubicB11Formula
public import IdealGeneration.CubicPrimitiveSplit
public import IdealGeneration.CubicIntegerSpecialization

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The fixed initial-pool determinant is a nonzero fiber at every later pair step. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B7Root

open B5 RationalChart CubicRationalFormula CubicParameterCompatibility CubicMixedLocality
open QuadraticTraceRestriction (extendPoint extendPoint_embedded extendPoint_off)

variable {K : Type*} [Field K] {k : ℕ}

abbrev PoolSampleIndex := Fin 43 ⊕ Fin 37

/-- The two components of each of the eighty fixed pool probes. -/
def poolSampleIndex : Index ≃ PoolSampleIndex × Fin 2 where
  toFun
    | .inl i => (.inl (rowIndex (n := 43) i).1, (rowIndex (n := 43) i).2)
    | .inr i => (.inr (rowIndex (n := 37) i).1, (rowIndex (n := 37) i).2)
  invFun
    | (.inl i, r) => .inl (finProdFinEquiv (i, r))
    | (.inr i, r) => .inr (finProdFinEquiv (i, r))
  left_inv := by
    intro i
    cases i <;> simp [rowIndex]
  right_inv := by
    rintro ⟨i | i, r⟩ <;> simp [rowIndex]

private def sample : PoolSampleIndex → Fin 10 × Option (Fin 10 × ℕ) :=
  Sum.elim point0 point1

private def direction : PoolSampleIndex → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The fixed pool points are extended by zero outside the initial ten coordinates. -/
def laterPoolPoint (K : Type*) [Field K] (k : ℕ) (i : PoolSampleIndex) : Fin (10 + 2 * k) → K :=
  extendPoint K (poolOldEmbedding k) fun j => sampleCoordinate (sample i) j

def laterPoolWeight (K : Type*) [Field K] (i : PoolSampleIndex) : Fin 2 → K :=
  pureDirection (direction i)

/-- The original pool rows and columns in the enlarged trace space. -/
def laterPool (K : Type*) [Field K] (k : ℕ) : PoolBlockData K (10 + 2 * k) Index where
  probe r := ⟨laterPoolPoint K k (poolSampleIndex r).1, laterPoolWeight K (poolSampleIndex r).1,
    (poolSampleIndex r).2⟩
  column r := embedPoolColumn k ((pool K).column r)
  supported r i hi := extendPoint_off K (poolOldEmbedding k) _ (by
    rintro ⟨j, rfl⟩
    exact (not_le_of_gt j.isLt) hi)
  columnPool r := embedPoolColumn_owner k ((pool K).column r)

theorem laterPool_probe (K : Type*) [Field K] (k : ℕ) (r : Index) :
    (laterPool K k).probe r =
      ⟨laterPoolPoint K k (poolSampleIndex r).1, laterPoolWeight K (poolSampleIndex r).1,
        (poolSampleIndex r).2⟩ := rfl

/-- Actual later pool entries agree with the original finite chart on matching data. -/
theorem laterPoolMatrix_eq {S : Parameters K 12} {L : Parameters K ((10 + 2 * k) + 2)}
    (agree : ∀ c, AgreesAt S L (poolExtendedEmbedding k) (poolExtendedEmbedding_strictMono k) c) :
    poolMatrix (actualB7Data L) (laterPool K k) = poolMatrix (actualB7Data S) (pool K) := by
  ext i j
  cases i
  · exact b7Value_poolTransport agree _ _ _ _
  · exact b7Value_poolTransport agree _ _ _ _

private def laterPoolFormula (k : ℕ) (r : Index) :
    B11ProbeFormula (NewPrimitiveIndex (10 + 2 * k) ⊕ PrimitiveIndex (10 + 2 * k)) (10 + 2 * k) :=
  let i := (poolSampleIndex r).1
  { support := (sampleSupport (sample i)).map (poolOldEmbedding k)
    point := Function.extend (poolOldEmbedding k) (fun j => (sampleCoordinate (sample i) j : Formula _))
      (fun _ => 0)
    weight := fun b => if b = direction i then 1 else 0
    component := (poolSampleIndex r).2 }

private theorem laterPoolFormula_matches
    (x : NewPrimitiveIndex (10 + 2 * k) ⊕ PrimitiveIndex (10 + 2 * k) → K) (r : Index) :
    (laterPoolFormula k r).Matches x ((laterPool K k).probe r) := by
  let i := (poolSampleIndex r).1
  constructor
  · intro j hj
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hj
    change Formula.Matches x
      (Function.extend (poolOldEmbedding k)
        (fun j => (sampleCoordinate (sample i) j : Formula _)) (fun _ => 0) (poolOldEmbedding k z))
      (extendPoint K (poolOldEmbedding k) (fun j => (sampleCoordinate (sample i) j : K))
        (poolOldEmbedding k z))
    rw [(poolOldEmbedding k).injective.extend_apply, extendPoint_embedded]
    exact Formula.Matches.natCast x _
  · intro j hj
    change extendPoint K (poolOldEmbedding k) (fun j => (sampleCoordinate (sample i) j : K)) j = 0
    by_cases he : j ∈ Set.range (poolOldEmbedding k)
    · obtain ⟨z, rfl⟩ := he
      rw [extendPoint_embedded]
      have hz : z ∉ sampleSupport (sample i) := fun hm => hj (Finset.mem_map.mpr ⟨z, hm, rfl⟩)
      rw [sampleCoordinate_eq_zero _ _ hz, Nat.cast_zero]
    · exact extendPoint_off K (poolOldEmbedding k) _ he
  · intro b
    change Formula.Matches x (if b = direction i then 1 else 0) (pureDirection (direction i) b)
    by_cases hb : b = direction i
    · simpa [pureDirection, hb] using Formula.Matches.ofNat x 1
    · simpa [pureDirection, hb] using Formula.Matches.ofNat x 0
  · rfl

/-- The denominator-cleared pool matrix polynomial in split primitive coordinates. -/
def laterPoolCertificate (k : ℕ) :
    MvPolynomial (NewPrimitiveIndex (10 + 2 * k) ⊕ PrimitiveIndex (10 + 2 * k)) ℤ :=
  b11Certificate (splitPrimitiveVariable (10 + 2 * k)) B5.single (laterPoolFormula k)
    (fun r => embedPoolColumn k ((pool ℚ).column r))

/-- The fixed-old pool polynomial in the current new primitive parameters. -/
def laterPoolFiber (P : Parameters K (10 + 2 * k)) :
    MvPolynomial (NewPrimitiveIndex (10 + 2 * k)) K :=
  specialize (primitiveValue P) (intSumPolynomial K (laterPoolCertificate k))

/-- On actual compatible cone data, the specialized polynomial detects the pool determinant. -/
theorem eval_laterPoolFiber_ne_zero_iff
    {P : Parameters K (10 + 2 * k)} {Q : Parameters K ((10 + 2 * k) + 2)}
    (h : Compatible P Q) (hQ : Q.single = B5.single) :
    MvPolynomial.eval (fun i : NewPrimitiveIndex (10 + 2 * k) => primitiveValue Q i.val)
      (laterPoolFiber P) ≠ 0 ↔ (poolMatrix (actualB7Data Q) (laterPool K k)).det ≠ 0 := by
  rw [laterPoolFiber, eval_specialize_intSumPolynomial, laterPoolCertificate, ← hQ]
  exact eval_b11Certificate_ne_zero_iff Q _ _ (splitPrimitiveVariable_matches h)
    (laterPoolFormula k) (laterPool K k).probe
    (fun r => embedPoolColumn k ((pool ℚ).column r)) (laterPoolFormula_matches _)

section Witness

variable [CharZero K]
variable {P : Parameters K (10 + 2 * k)} {L : Parameters K ((10 + 2 * k) + 2)}

private theorem poolPrefixAgreement_of_compatible (hP : AgreesInitialPool P) (h : Compatible P L) :
    PoolPrefixAgreement (parametersCharZero K) L := by
  constructor
  · intro c hc
    let i : Fin 10 := ⟨c.val, hc⟩
    have he : Fin.castAdd 2 i = c := Fin.ext rfl
    rw [← he, poolExtendedEmbedding_old]
    exact ⟨funext (fun d =>
      (initialCompatible K).vertexSlope_eq i d |>.trans
        ((congrFun (hP i).vertexSlope_eq d).trans (h.vertexSlope_eq _ d).symm)),
      funext (fun d =>
      (initialCompatible K).vertexHeight_eq i d |>.trans
        ((congrFun (hP i).vertexHeight_eq d).trans (h.vertexHeight_eq _ d).symm))⟩
  · intro e he
    let a : Edge 10 := ⟨(⟨e.val.1.val, lt_trans e.property he⟩, ⟨e.val.2.val, he⟩), e.property⟩
    have ha : oldEdge 10 a = e := Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext rfl))
    rw [← ha]
    let ap := edgeImage (poolOldEmbedding k) (poolOldEmbedding_strictMono k) a
    have himg : poolExtendedEdge k (oldEdge 10 a) = oldEdge (10 + 2 * k) ap :=
      Subtype.ext (Prod.ext (poolExtendedEmbedding_old k a.val.1) (poolExtendedEmbedding_old k a.val.2))
    rw [himg]
    obtain ⟨_, hl, hs, hh⟩ := (hP a.val.1).edge_eq a (Or.inl rfl)
    exact ⟨(initialCompatible K).edgeLambda_eq a |>.trans (hl.trans (h.edgeLambda_eq ap).symm),
      funext (fun d => (initialCompatible K).edgeSlope_eq a d |>.trans
        ((congrFun hs d).trans (h.edgeSlope_eq ap d).symm)),
      funext (fun d => (initialCompatible K).edgeHeight_eq a d |>.trans
        ((congrFun hh d).trans (h.edgeHeight_eq ap d).symm))⟩

/-- The original pool witness gives a nonzero new-coordinate polynomial at every retained pool. -/
theorem laterPoolFiber_ne_zero (hP : AgreesInitialPool P) (h : Compatible P L)
    (hL : L.single = B5.single)
    (hroot : (poolMatrix (actualB7Data (parametersCharZero K)) (pool K)).det ≠ 0) :
    laterPoolFiber P ≠ 0 := by
  let Q := withPoolParameters (parametersCharZero K) L (fun _ => rfl) (fun e => congrFun hL e)
  have hcompat : Compatible P Q :=
    withPoolParameters_compatible (parametersCharZero K) L (fun _ => rfl) (fun e => congrFun hL e) h
  have hagree := agreesAt_withPoolParameters (parametersCharZero K) L (fun _ => rfl)
    (fun e => congrFun hL e) (poolPrefixAgreement_of_compatible hP h)
  have heval := (eval_laterPoolFiber_ne_zero_iff hcompat hL).mpr (by
    rw [laterPoolMatrix_eq hagree]
    exact hroot)
  intro hz
  exact heval (hz ▸ map_zero (MvPolynomial.eval (fun i : NewPrimitiveIndex (10 + 2 * k) => primitiveValue Q i.val)))

end Witness
end IdealGeneration.CubicSupported.B7Root
