module

public import IdealGeneration.BoundedGeneration

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The numerical generator statement on the same open as maximal-rank multiplication. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {n p d : ℕ}

local instance generatorPieceGroup (a : PointCoordinates K n p) (e : ℕ) :
    AddCommGroup (pointDegreePiece K a e) := Module.addCommMonoidToAddCommGroup K

/-- The degree immediately above the initial equations has the generator
quotient dimension stated in Theorem 1.1. -/
theorem point_next_generator_dimension (a : PointCoordinates K n p)
    (hp : p ≤ N (n + 1) d)
    (hd : pointHilbertFunction K a d = min (N (n + 1) d) p)
    (hd1 : pointHilbertFunction K a (d + 1) = min (N (n + 1) (d + 1)) p)
    (hm : HasMaximalRank (pointMultiplication a d)) :
    (finrank K ((pointDegreePiece K a (d + 1)) ⧸ (pointMultiplication a d).range) : ℚ) =
      max 0 ((n : ℚ) * (E (n + 1) d - (N (n + 1) d - p : ℕ))) := by
  rw [pointMultiplication_cokernel_dimension a hd hd1 hm]
  have hp' : p ≤ N (n + 1) (d + 1) := hp.trans
    (by simpa only [Nat.add_sub_cancel] using N_pred_le (n + 1) (d + 1) (by omega) (by omega))
  let x := N (n + 1) (d + 1) - p
  let y := (n + 1) * (N (n + 1) d - p)
  have hcast : ((x - y : ℕ) : ℚ) = max 0 ((x : ℚ) - y) := by
    rcases le_total y x with h | h
    · rw [Nat.cast_sub h, max_eq_right]
      exact sub_nonneg.mpr (by exact_mod_cast h)
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, max_eq_left]
      exact sub_nonpos.mpr (by exact_mod_cast h)
  change ((x - y : ℕ) : ℚ) = _
  rw [hcast]
  simp only [x, y, Nat.cast_sub hp', Nat.cast_mul, Nat.cast_sub hp, Nat.cast_add, Nat.cast_one]
  simpa using next_generator_count_formula (n + 1) d p (by omega)

/-- The initial piece, next generator quotient, and actual two-degree
generation are controlled on a single nonempty principal open. -/
theorem idealGenerationAt_exact_generator_dimensions [CharZero K]
    (hd : 1 ≤ d) (hp0 : N (n + 1) (d - 1) ≤ p) (hp : p ≤ N (n + 1) d)
    (h : IdealGenerationAt K n d p) :
    ∃ Δ : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 →
        finrank K (pointDegreePiece K a d) = N (n + 1) d - p ∧
        (finrank K ((pointDegreePiece K a (d + 1)) ⧸
          (pointMultiplication a d).range) : ℚ) =
          max 0 ((n : ℚ) * (E (n + 1) d - (N (n + 1) d - p : ℕ))) ∧
        pointIdeal K a = Ideal.span (twoDegreePointEquations a d) := by
  obtain ⟨Δ, hΔ, hgood⟩ := h
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  obtain ⟨_, hpost, hm⟩ := hgood a ha
  have hpost' (e : ℕ) : pointHilbertFunction K a e = min (N (n + 1) e) p := by
    simpa only [N_chart] using hpost e
  exact ⟨pointDegreePiece_finrank a (hpost' d),
    point_next_generator_dimension a hp (hpost' d) (hpost' (d + 1)) hm,
    pointIdeal_eq_span_two_degrees a d hd hpost' hp0 hp⟩

end IdealGeneration
