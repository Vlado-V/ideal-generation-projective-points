module

public import IdealGeneration.CubicAllowedValues
public import IdealGeneration.CubicSupportedAmbientDimensions
public import IdealGeneration.CubicSupportedKernel
public import IdealGeneration.CubicSupportedPattern
public import IdealGeneration.Numerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Label and parameter counts for the even supported family of Appendix B. -/

namespace IdealGeneration.CubicSupported.B5

/-- Free trace supports at the level with `10 + 2*k` trace variables. -/
def freeCount (k : ℕ) : ℕ := (10 + 2 * k + 1) * (k + 5).choose 2

private theorem twice_choose_two (n : ℕ) : 2 * (n + 1).choose 2 = (n + 1) * n := by
  simpa only [Nat.choose_one_right, Nat.mul_comm 2] using
    (Nat.add_one_mul_choose_eq n 1).symm

private theorem twice_freeCount (k : ℕ) :
    2 * freeCount k = (10 + 2 * k + 1) * ((k + 5) * (k + 4)) := by
  unfold freeCount
  calc
    _ = (10 + 2 * k + 1) * (2 * (k + 5).choose 2) := by ring
    _ = _ := by rw [twice_choose_two (k + 4)]

/-- The free-support count is the integer form of the formula in (B.3). -/
theorem freeCount_eq_paper (k : ℕ) :
    freeCount k = (10 + 2 * k) * (10 + 2 * k + 1) * (10 + 2 * k - 2) / 8 := by
  have h : (10 + 2 * k) * (10 + 2 * k + 1) * (10 + 2 * k - 2) = freeCount k * 8 := by
    rw [show 10 + 2 * k - 2 = 8 + 2 * k by omega,
      show freeCount k * 8 = 4 * (2 * freeCount k) by ring, twice_freeCount]
    ring
  rw [h, Nat.mul_div_cancel _ (by decide)]

/-- The number of increasing edges at the even level. -/
theorem card_edge_even (k : ℕ) : Fintype.card (Edge (10 + 2 * k)) = (k + 5) * (2 * k + 9) := by
  have h := two_mul_card_edge_add (10 + 2 * k)
  have he : 2 * ((k + 5) * (2 * k + 9)) + (10 + 2 * k) =
      (10 + 2 * k) * (10 + 2 * k) := by ring
  omega

variable {K : Type*} [Field K]

/-- Parameters with the B.5 single-edge pattern have the prescribed single-edge count. -/
theorem card_singleEdges (k : ℕ) (P : Parameters K (10 + 2 * k)) (hs : P.single = single) :
    Fintype.card P.SingleEdge = k * k + 6 * k + 2 := by
  let e : P.SingleEdge ≃ {e : Edge (10 + 2 * k) // single e = true} :=
    Equiv.subtypeEquivRight (fun e => by rw [hs])
  exact (Fintype.card_congr e).trans (card_single k)

/-- There are `3*(k+6)^2` attached cone points at the even level. -/
theorem card_coneLabel_even (k : ℕ) (P : Parameters K (10 + 2 * k)) (hs : P.single = single) :
    Fintype.card P.ConeLabel = 3 * (k + 6) ^ 2 := by
  rw [P.card_coneLabel, card_singleEdges k P hs, card_edge_even]
  have h : 2 * (10 + 2 * k) + 2 * ((k + 5) * (2 * k + 9)) =
      3 * (k + 6) ^ 2 + (k * k + 6 * k + 2) := by ring
  omega

/-- The trace labels count vertices, increasing edges, and the free supports. -/
theorem card_traceLabel_even (k : ℕ) :
    Fintype.card (TraceLabel (10 + 2 * k) (freeCount k)) =
      (10 + 2 * k + 1) * (k + 6).choose 2 := by
  rw [card_traceLabel, card_edge_even, freeCount, Nat.choose_succ_succ' (k + 5) 1,
    Nat.choose_one_right]
  ring

/-- The number of trace labels is exactly three quarters of the cubic monomial count. -/
theorem four_mul_card_traceLabel (k : ℕ) :
    4 * Fintype.card (TraceLabel (10 + 2 * k) (freeCount k)) = 3 * N (10 + 2 * k) 3 := by
  rw [card_traceLabel_even]
  calc
    _ = 2 * (10 + 2 * k + 1) * (2 * (k + 6).choose 2) := by ring
    _ = 2 * (10 + 2 * k + 1) * ((k + 6) * (k + 5)) := by rw [twice_choose_two (k + 5)]
    _ = (k + 6) * ((10 + 2 * k + 1) * (10 + 2 * k)) := by ring
    _ = (k + 6) * (2 * (10 + 2 * k + 1).choose 2) := by rw [twice_choose_two (10 + 2 * k)]
    _ = (10 + 2 * k + 2) * (10 + 2 * k + 1).choose 2 := by ring
    _ = _ := by
      unfold N
      rw [show 10 + 2 * k + 3 - 1 = 10 + 2 * k + 2 by omega, Nat.mul_comm 3]
      exact Nat.add_one_mul_choose_eq (10 + 2 * k + 1) 2

/-- The coefficient kernel has `(k+6)^2` independent coordinates. -/
theorem finrank_coefficientKernel_even (k : ℕ) (P : Parameters K (10 + 2 * k))
    (hs : P.single = single) : Module.finrank K P.coefficientKernel = (k + 6) ^ 2 := by
  rw [P.finrank_coefficientKernel, card_singleEdges k P hs]
  ring

/-- The independent-parameter count `(2*dim K-5) + 3*card Edge + m*card SingleEdge` from (B.2). -/
def eliminatedParameterCount (k : ℕ) : ℕ :=
  (2 * (k + 6) ^ 2 - 5) + 3 * (10 + 2 * k).choose 2 + (10 + 2 * k) * (k * k + 6 * k + 2)

/-- Express the B.2 count directly in terms of the actual supported coefficient kernel and graph. -/
theorem eliminatedParameterCount_eq (k : ℕ) (P : Parameters K (10 + 2 * k))
    (hs : P.single = single) :
    (2 * Module.finrank K P.coefficientKernel - 5) +
      3 * Fintype.card (Edge (10 + 2 * k)) + (10 + 2 * k) * Fintype.card P.SingleEdge =
        eliminatedParameterCount k := by
  simp only [eliminatedParameterCount, finrank_coefficientKernel_even k P hs,
    card_edge, card_singleEdges k P hs]

private theorem eliminatedParameterCount_poly (k : ℕ) :
    eliminatedParameterCount k = 2 * k ^ 3 + 30 * k ^ 2 + 145 * k + 222 := by
  have he : (10 + 2 * k).choose 2 = (k + 5) * (2 * k + 9) :=
    (card_edge (10 + 2 * k)).symm.trans (card_edge_even k)
  have hbase : 2 * (k + 6) ^ 2 - 5 = 2 * k ^ 2 + 24 * k + 67 := by
    rw [show 2 * (k + 6) ^ 2 = (2 * k ^ 2 + 24 * k + 67) + 5 by ring]
    omega
  rw [eliminatedParameterCount, he, hbase]
  ring

/-- The actual allowed-value target has the same dimension as the B.2 parameter count. -/
theorem finrank_allowedValues_even (k : ℕ) (P : Parameters K (10 + 2 * k))
    (hs : P.single = single) (free : Fin (freeCount k) → Fin (10 + 2 * k) → K) :
    Module.finrank K (CubicMiddle.allowedValues (P.toConeConfiguration free)) =
      eliminatedParameterCount k := by
  rw [P.finrank_allowedValues free, card_singleEdges k P hs, twice_freeCount,
    eliminatedParameterCount_poly]
  ring

private theorem three_mul_sq_div_two (k : ℕ) :
    3 * (10 + 2 * k) * (10 + 2 * k) / 2 = 3 * (10 + 2 * k) * (k + 5) := by
  rw [show 3 * (10 + 2 * k) * (10 + 2 * k) = (3 * (10 + 2 * k) * (k + 5)) * 2 by ring,
    Nat.mul_div_cancel _ (by decide)]

/-- Adding the next pair contributes `3*m²/2 + 3*m - 3` independent B.2 parameters. -/
theorem eliminatedParameterCount_step (k : ℕ) :
    eliminatedParameterCount (k + 1) - eliminatedParameterCount k =
      3 * (10 + 2 * k) * (10 + 2 * k) / 2 + 3 * (10 + 2 * k) - 3 := by
  rw [eliminatedParameterCount_poly (k + 1), eliminatedParameterCount_poly k, three_mul_sq_div_two]
  have h₁ : 2 * (k + 1) ^ 3 + 30 * (k + 1) ^ 2 + 145 * (k + 1) + 222 =
      (2 * k ^ 3 + 30 * k ^ 2 + 145 * k + 222) + (6 * k ^ 2 + 66 * k + 177) := by ring
  have h₂ : 3 * (10 + 2 * k) * (k + 5) + 3 * (10 + 2 * k) =
      (6 * k ^ 2 + 66 * k + 177) + 3 := by ring
  omega

/-- There are `m-3` new single edges after adding a pair. -/
theorem card_single_step (k : ℕ) :
    Fintype.card {e : Edge (10 + 2 * (k + 1)) // single e = true} -
      Fintype.card {e : Edge (10 + 2 * k) // single e = true} = 10 + 2 * k - 3 := by
  rw [card_single (k + 1), card_single k]
  have h : (k + 1) * (k + 1) + 6 * (k + 1) + 2 = (k * k + 6 * k + 2) + (2 * k + 7) := by ring
  omega

/-- Two higher-order columns per new single edge and three normal quadratics give `2*m-3`. -/
theorem higherParameterCount (k : ℕ) :
    2 * (Fintype.card {e : Edge (10 + 2 * (k + 1)) // single e = true} -
      Fintype.card {e : Edge (10 + 2 * k) // single e = true}) + 3 = 2 * (10 + 2 * k) - 3 := by
  rw [card_single_step]
  omega

/-- Removing the higher-order columns leaves the `3*m²/2 + m` linear-part columns. -/
theorem lowerParameterCount (k : ℕ) :
    (eliminatedParameterCount (k + 1) - eliminatedParameterCount k) - (2 * (10 + 2 * k) - 3) =
      3 * (10 + 2 * k) * (10 + 2 * k) / 2 + (10 + 2 * k) := by
  rw [eliminatedParameterCount_step]
  omega

private theorem three_mul_sq_div_four (k : ℕ) :
    3 * (10 + 2 * k) * (10 + 2 * k) / 4 = 3 * (k + 5) ^ 2 := by
  rw [show 3 * (10 + 2 * k) * (10 + 2 * k) = (3 * (k + 5) ^ 2) * 4 by ring,
    Nat.mul_div_cancel _ (by decide)]

/-- The number of newly available free trace supports. -/
theorem freeCount_step (k : ℕ) : freeCount (k + 1) - freeCount k =
    3 * (10 + 2 * k) * (10 + 2 * k) / 4 + (10 + 2 * k) := by
  rw [three_mul_sq_div_four]
  have h : 2 * freeCount (k + 1) = 2 * freeCount k + 2 * (3 * (k + 5) ^ 2 + (10 + 2 * k)) := by
    rw [twice_freeCount (k + 1), twice_freeCount k]
    ring
  omega

/-- The new free supports split into the lower-block group and the `m/2` higher-block group. -/
theorem freeCount_step_split (k : ℕ) : freeCount (k + 1) - freeCount k =
    (3 * (10 + 2 * k) * (10 + 2 * k) / 4 + (10 + 2 * k) / 2) + (10 + 2 * k) / 2 := by
  rw [freeCount_step]
  omega

end IdealGeneration.CubicSupported.B5
