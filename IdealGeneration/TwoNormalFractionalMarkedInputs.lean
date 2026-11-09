module

public import IdealGeneration.TwoNormalFractionalTraceOpen
public import IdealGeneration.TwoNormalFractionalMotion
public import IdealGeneration.TwoNormalMarkedCode
public import IdealGeneration.TwoNormalIntegralInputs

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # Simultaneous marked interpolation for the fractional transfer -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial Module TwoNormalIntegral TwoNormalSlice TwoNormalTrace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n d b q l g : ℕ}

/-- A rank predicate containing a witnessed principal open. -/
def ContainsPrincipalOpen {ι : Type*} (R : (ι → K) → Prop) : Prop :=
  ∃ P : MvPolynomial ι K, (∃ c, eval c P ≠ 0) ∧ ∀ c, eval c P ≠ 0 → R c

theorem ContainsPrincipalOpen.mono {ι : Type*} {R S : (ι → K) → Prop}
    (h : ContainsPrincipalOpen R) (hrs : ∀ c, R c → S c) : ContainsPrincipalOpen S := by
  obtain ⟨P, hP, hgood⟩ := h
  exact ⟨P, hP, fun c hc => hrs c (hgood c hc)⟩

theorem ContainsPrincipalOpen.inter [Infinite K] {ι : Type*} {R S : (ι → K) → Prop}
    (hR : ContainsPrincipalOpen R) (hS : ContainsPrincipalOpen S) :
    ContainsPrincipalOpen (fun c => R c ∧ S c) := by
  obtain ⟨P, hP, hp⟩ := hR
  obtain ⟨Q, hQ, hq⟩ := hS
  obtain ⟨c₀, hcP, hcQ⟩ := principal_opens_meet P Q hP hQ
  refine ⟨P * Q, ⟨c₀, by simpa using mul_ne_zero hcP hcQ⟩, ?_⟩
  intro c hc
  have hparts : eval c P ≠ 0 ∧ eval c Q ≠ 0 := by simpa using hc
  exact ⟨hp c hparts.1, hq c hparts.2⟩

theorem ContainsPrincipalOpen.pull {ι κ : Type*} {R : (ι → K) → Prop}
    (h : ContainsPrincipalOpen R) (e : ι ↪ κ) :
    ContainsPrincipalOpen (fun c => R (c ∘ e)) := by
  obtain ⟨P, hP, hgood⟩ := h
  obtain ⟨h₀, h₁⟩ := principalOpen_pullback e P hP
  exact ⟨rename e P, h₀, fun c hc => hgood _ (h₁ c hc)⟩

private abbrev trSize (b q l : ℕ) := b + (b + (q + l))
private abbrev codeSize (n b d : ℕ) := (n + 1) * (N (n + 2) (d + 1) - b)

private abbrev fA (c : FractionalParameters K n b q l) := markedSliceA (c ∘ Sum.inl)
private abbrev fB (c : FractionalParameters K n b q l) := markedSliceB (c ∘ Sum.inl)
private abbrev fZ (c : FractionalParameters K n b q l) := chartPoint K (fractionalTraceCoordinates c)

private theorem sliceProductSpace_dimension
    (a : PointCoordinates K (n + 1) b) (ha : IntegralSliceGood a d) :
    codeSize n b d = finrank K (sliceProductSpace a d) := by
  change _ = finrank K (tangentPointProductForm a (d + 1)).range
  rw [finrank_tangentPointProductForm_range a ha.normal ha.multiplication, ha.dimension]

/-- Scalar ranks on a slice, its trace evaluation, and its quotient classes. -/
structure FractionalSliceCodeGood
    (a : PointCoordinates K (n + 1) b) (z : Fin (trSize b q l) → Fin (n + 1) → K)
    (d : ℕ) : Prop where
  slice : IntegralSliceGood a d
  evaluation : Function.Injective ((scalarEvaluation z (d + 1 + 1)).comp
    (tangentPointProductForm a (d + 1)).range.subtype)
  coordinates : ∀ (r : ℕ) (f : Fin r ↪ Fin (trSize b q l)),
    r ≤ finrank K (TraceProductQuotient a z (d + 1)) →
    LinearIndependent K (traceProductCoordinate a z (d + 1) ∘ f)

private theorem traceProductCoordinate_eq_class
    (a : PointCoordinates K (n + 1) b) (z : Fin (trSize b q l) → Fin (n + 1) → K)
    (e : ℕ) (i : Fin (trSize b q l)) :
    traceProductCoordinate a z e i = coordinateClass (traceProductCodeMap a z e) i := by
  classical
  apply congrArg (traceProductCodeMap a z e).range.mkQ
  funext j
  by_cases hij : j = i <;> simp [hij]

/-- Both slice codes satisfy the required ranks on one principal open. -/
theorem fractional_slice_codes_open [CharZero K]
    (hSlice : ContainsPrincipalOpen (fun a : PointCoordinates K (n + 1) b =>
      IntegralSliceGood a d)) (hcount : codeSize n b d ≤ trSize b q l) :
    ContainsPrincipalOpen (fun c : FractionalParameters K n b q l =>
      FractionalSliceCodeGood (q := q) (l := l) (fA c) (fZ c) d ∧
        FractionalSliceCodeGood (q := q) (l := l) (fB c) (fZ c) d) := by
  obtain ⟨P, hP, hp⟩ := hSlice
  obtain ⟨a₀, ha₀⟩ := hP
  have ha := hp a₀ ha₀
  have hcodes := generic_markedSliceCodes_unisolvent (q := q) (l := l) a₀ a₀
    ha.normal ha.normal ha.multiplication ha.multiplication ha.projectedScalar ha.projectedScalar
    (sliceProductSpace_dimension a₀ ha) (sliceProductSpace_dimension a₀ ha)
  let iL : MarkedIndex n b q l ↪ FractionalIndex n b q l := Function.Embedding.inl
  let eA : (Fin b × Fin (n + 1)) ↪ MarkedIndex n b q l := Function.Embedding.inl
  let eB : (Fin b × Fin (n + 1)) ↪ MarkedIndex n b q l :=
    Function.Embedding.inl.trans Function.Embedding.inr
  let iA := eA.trans iL
  let iB := eB.trans iL
  have hSlice' : ContainsPrincipalOpen (fun a : PointCoordinates K (n + 1) b =>
      IntegralSliceGood a d) := ⟨P, ⟨a₀, ha₀⟩, hp⟩
  have hA : ContainsPrincipalOpen (fun c : FractionalParameters K n b q l =>
      IntegralSliceGood (fA c) d) := hSlice'.pull iA
  have hB : ContainsPrincipalOpen (fun c : FractionalParameters K n b q l =>
      IntegralSliceGood (fB c) d) := hSlice'.pull iB
  have hC : ContainsPrincipalOpen (fun c : FractionalParameters K n b q l =>
      ∀ f : Fin (codeSize n b d) ↪ Fin (trSize b q l),
        Function.Injective (subspaceEvaluation (sliceProductSpace (fA c) d)
          (selectedTraceCoordinates (fractionalTraceCoordinates c) f)) ∧
        Function.Injective (subspaceEvaluation (sliceProductSpace (fB c) d)
          (selectedTraceCoordinates (fractionalTraceCoordinates c) f))) :=
    ContainsPrincipalOpen.pull hcodes iL
  apply ((hA.inter hB).inter hC).mono
  rintro c ⟨⟨ha, hb⟩, hselected⟩
  obtain ⟨hevalA, hcoordA⟩ := orderedTraceProduct_coordinateClasses (fA c)
    (fractionalTraceCoordinates c) ha.normal ha.multiplication
    (sliceProductSpace_dimension (fA c) ha) hcount (fun f => (hselected f).1)
  obtain ⟨hevalB, hcoordB⟩ := orderedTraceProduct_coordinateClasses (fB c)
    (fractionalTraceCoordinates c) hb.normal hb.multiplication
    (sliceProductSpace_dimension (fB c) hb) hcount (fun f => (hselected f).2)
  refine ⟨⟨ha, hevalA, ?_⟩, ⟨hb, hevalB, ?_⟩⟩
  · intro k f hk
    simpa only [Function.comp_def, traceProductCoordinate_eq_class] using hcoordA k f hk
  · intro k f hk
    simpa only [Function.comp_def, traceProductCoordinate_eq_class] using hcoordB k f hk

end IdealGeneration.TwoNormalFractional
