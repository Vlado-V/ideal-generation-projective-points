module

public import IdealGeneration.TwoNormalFractionalCountAssembly
public import IdealGeneration.TwoNormalFractionalAttachments
public import IdealGeneration.TwoNormalFractionalEnlargedOpen
public import IdealGeneration.TwoNormalFractionalDimensionBalance
public import IdealGeneration.TwoNormalEndpoint
public import IdealGeneration.CriticalOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # Fractional two-normal transfer, Proposition 5.1 -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial Module TwoNormalTrace TwoNormalSlice
open TwoNormalIntegral hiding sliceCount
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] [CharZero K]

/-- The fractional trace construction gives either ambient critical count. -/
theorem fractional_twoNormal_endpoint (n d r : ℕ)
    (hn : 1 ≤ n) (hD : 4 ≤ d + 1 + 1)
    (hm₀ : (d + 1 + 1) * (d + 1 + 1 - 1) ≤ n + 1)
    (hf : ¬ ∃ t : ℕ, E (n + 1) (d + 1 + 1) = (t : ℚ))
    (hr : r = lowerCritical (n + 3) (d + 1 + 1) ∨
      r = upperCritical (n + 3) (d + 1 + 1))
    (hSlice : ∀ p, IdealGenerationAt K (n + 1) (d + 1) p)
    (hResidual : ∀ p, IdealGenerationAt K n d p)
    (hTrace : ∀ p, IdealGenerationAt K n (d + 1 + 1) p) :
    IdealGenerationAt K (n + 2) (d + 1 + 1) (N (n + 3) (d + 1 + 1) - r) := by
  let m := n + 1
  let D := d + 1 + 1
  let b := sliceCount m D
  let q := attachedOffCount m D r
  let l := extraTraceCount m D r
  let g := residualCount m D r
  let k := b + (b + (q + l))
  have hnum := fractionalCountFacts m D r hD hm₀ hf hr
  have hm : D * (D - 1) < m := fractional_dimension_strict m D hD hm₀ hf
  have hk : k = tracePointCount m D := hnum.traceSum
  have hq : q + 1 = offSlicePointCount m D r := hnum.offSum
  have hg : g ≤ N m d := Nat.le_trans (Nat.le_succ _) hnum.residualUpper
  have hgcrit : (g : ℚ) ≤ E m d := by
    have h : ((g + 1 : ℕ) : ℚ) ≤ E m d := hnum.residualCritical
    push_cast at h
    linarith
  have hXsum : q + 1 + g = N (n + 3) d := by
    rw [hq]
    exact hnum.fullResidualSum
  have hS := generic_integralSliceGood (K := K) hn d b hnum.sliceLower
    hnum.sliceUpper hnum.sliceTraceUpper hnum.sliceCritical (hSlice b)
  have hX := generic_integralOffSliceGood (K := K) hn d (q + 1) g hg hXsum hgcrit
    (hResidual _)
  obtain ⟨P, ⟨x₀, hx₀⟩, hP⟩ := generic_integralOffSliceGood (K := K) hn d q (g + 1)
    hnum.residualUpper hnum.attachedResidualSum hnum.residualCritical (hResidual _)
  have hx := hP x₀ hx₀
  have hE := fractional_enlarged_open (l := l) (b := b) x₀ hx.trace hx.product
    (by rw [hx.dimension]; exact hnum.pureBudget)
  have hcells := trace_initialDegreeCells m D (by omega) (by omega) hf
  have htraceP : k + 1 ≤ N m D := by rw [hk]; exact hcells.2.le
  have htraceL : N m (D - 1) ≤ k := hk.symm ▸ hcells.1
  have hu : upperCritical m D ≤ N m D :=
    (upperCritical_mem_cell m D (by omega) (by omega)).2.trans (Nat.sub_le _ _)
  have hl : lowerCritical m D ≤ N m D :=
    (lowerCritical_mem_cell m D (by omega) (by omega)).2.trans (Nat.sub_le _ _)
  have htraceCritS : E m D ≤ ((N m D - k : ℕ) : ℚ) := by
    rw [hk, tracePointCount, Nat.sub_sub_self hu]
    exact (E_le_iff_upperCritical_le _ _ _).mpr le_rfl
  have htraceCritI : ((N m D - (k + 1) : ℕ) : ℚ) ≤ E m D := by
    rw [hk, tracePointCount_add_one m D (by omega) (by omega) hf, Nat.sub_sub_self hl]
    exact (le_E_iff_le_lowerCritical _ _ _).mpr le_rfl
  have hT : ContainsPrincipalOpen (fun c : FractionalParameters K n b q l =>
      FractionalTraceGood c d) := by
    obtain ⟨T, hT, hTgood⟩ := fractional_trace_open (b := b) (q := q) (l := l) (D := D)
      hn htraceP htraceL htraceCritS htraceCritI (hTrace k) (hTrace (k + 1))
    exact ⟨T, hT, fun c hc => by
      obtain ⟨he, hi, hs, hl⟩ := hTgood c hc
      exact ⟨he, hi, hs, hl⟩⟩
  have hcodeBudget : (n + 1) * (N (n + 2) (d + 1) - b) ≤ k := by
    rw [hk]
    exact hnum.codeBudget
  have hpureBudget : (n + 2) * g ≤ b :=
    (Nat.mul_le_mul_left _ (Nat.le_succ g)).trans hnum.pureBudget
  have hpairBudget : 2 * b ≤ (n + 1) * g + (N (n + 3) (d + 1) - (q + 1)) := by
    rw [hq]
    exact hnum.pairBudget
  obtain ⟨c, hc⟩ := exists_fractionalMarkedGood (d := d) (g := g)
    hS hT hE hX hcodeBudget hpureBudget hpairBudget
  let a := markedSliceA (c ∘ Sum.inl)
  let a' := markedSliceB (c ∘ Sum.inl)
  let x := fractionalOffCoordinates c
  let z := chartPoint K (fractionalTraceCoordinates c)
  obtain ⟨hslice, hsource⟩ := fractional_conditions_of_marked c hc
  have hz (i : Fin k) : commonTracePoint (z i) (Fin.last (m + 1)) = 1 := by
    rw [show Fin.last (m + 1) = (Fin.last n).succ.succ by rfl]
    simp [z, commonTracePoint]
  have hG := hc.offSlice.scalar
  have hH := pointEvaluation_surjective_above x (Nat.le_succ d) hG
  have hnormal := normalFiberEvaluation_surjective_of_pair_surjective K m a a' x d
    hc.offSlice.sNonzero hc.offSlice.tNonzero hG hH hc.pair
  have hbalance := fractional_marked_dimension_balance (d := d) r hD hm hr a a' x z
    rfl hq hk hslice (Fin.last n) (fun i => by simp [z]) hc.trace.euler
    hc.firstSlice.slice.scalar hc.secondSlice.slice.scalar hG hH hc.pair
  obtain ⟨v, u, _, _, Q, hQ, hmotion⟩ := fractional_marked_fiber_transfer a a' x z hslice hsource hz
    hc.trace.euler hc.firstSlice.slice.scalar hc.secondSlice.slice.scalar hnormal
    hc.firstSlice.coordinates hc.secondSlice.coordinates hbalance
  have hscalar := markedScalarEvaluation_surjective_of_groups (d := d) a a' z x
    hc.firstSlice.slice.normal hc.secondSlice.slice.normal hc.offSlice.sNonzero hc.offSlice.tNonzero
    hc.firstSlice.slice.scalar hc.secondSlice.slice.scalar hG hc.trace.scalar
  have hresult := idealGenerationAt_of_marked_moving_evaluation (d := d) (by omega : 0 < m)
    a a' z x hz hscalar v u Q hQ hmotion
  have htotal : b + (b + (k + (q + 1))) = N (n + 3) D - r := by
    rw [hk, hq]
    exact hnum.ambientSum
  exact htotal ▸ hresult

/-- The two critical counts imply every count for the fractional transfer. -/
theorem idealGenerationAt_fractional_twoNormal (n d : ℕ)
    (hn : 1 ≤ n) (hD : 4 ≤ d + 1 + 1)
    (hm₀ : (d + 1 + 1) * (d + 1 + 1 - 1) ≤ n + 1)
    (hf : ¬ ∃ t : ℕ, E (n + 1) (d + 1 + 1) = (t : ℚ))
    (hSlice : ∀ p, IdealGenerationAt K (n + 1) (d + 1) p)
    (hResidual : ∀ p, IdealGenerationAt K n d p)
    (hTrace : ∀ p, IdealGenerationAt K n (d + 1 + 1) p) :
    ∀ p, IdealGenerationAt K (n + 2) (d + 1 + 1) p :=
  idealGenerationAt_all_of_critical (by omega) (by omega)
    (fractional_twoNormal_endpoint n d _ hn hD hm₀ hf (Or.inl rfl) hSlice hResidual hTrace)
    (fractional_twoNormal_endpoint n d _ hn hD hm₀ hf (Or.inr rfl) hSlice hResidual hTrace)

/-- Proposition 5.1 in ambient projective dimension and polynomial degree. -/
theorem proposition5_1 (n D : ℕ) (hD : 4 ≤ D) (hn : D * (D - 1) < n)
    (hf : ¬ ∃ t : ℕ, E (n - 1) D = (t : ℚ))
    (hSlice : ∀ p, IdealGenerationAt K (n - 1) (D - 1) p)
    (hResidual : ∀ p, IdealGenerationAt K (n - 2) (D - 2) p)
    (hTrace : ∀ p, IdealGenerationAt K (n - 2) D p) :
    ∀ p, IdealGenerationAt K n D p := by
  have hpos : 0 < D * (D - 1) := Nat.mul_pos (by omega) (by omega)
  have hbig : 3 ≤ n := by
    have hge := Nat.mul_le_mul_left D (show 3 ≤ D - 1 by omega)
    omega
  have hn₁ : n - 2 + 1 = n - 1 := by omega
  have hn₂ : n - 2 + 2 = n := by omega
  have hD₁ : D - 2 + 1 = D - 1 := by omega
  have hD₂ : D - 2 + 1 + 1 = D := by omega
  have hresult := idealGenerationAt_fractional_twoNormal (K := K) (n - 2) (D - 2)
    (by omega) (by omega) (by rw [hD₂, hn₁]; omega)
    (by simpa only [hn₁, hD₂] using hf)
    (by simpa only [hn₁, hD₁] using hSlice) hResidual
    (by simpa only [hD₂] using hTrace)
  simpa only [hn₂, hD₂] using hresult

end IdealGeneration.TwoNormalFractional
