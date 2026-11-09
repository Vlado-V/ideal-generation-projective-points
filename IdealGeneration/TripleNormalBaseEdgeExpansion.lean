module

public import IdealGeneration.TripleNormalEdgeOrder
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The base evaluation grouped by its supported edge and diagonal coefficients. -/

open scoped BigOperators

namespace IdealGeneration.TripleNormal.BaseEdgeExpansion

variable {K : Type*} [Field K] {h : ℕ}

/-- The coefficient of the edge joining an old coordinate to a new one. -/
def oldNewCoefficient
    (v : Fin (h + 3) → Fin 3 → K) (A : Fin (h + 3) → Fin 3 → Fin 3 → K)
    (ρ : Fin (h + 3 + 4) → Fin (h + 3) → K) (i : Fin h) (b : Fin 3) (a : Fin 3) : K :=
  ρ ((b.natAdd h).castAdd 4) (i.castAdd 3) * v (i.castAdd 3) a +
    ρ ((i.castAdd 3).castAdd 4) (b.natAdd h) * v (b.natAdd h) a - A (i.castAdd 3) b a

/-- The coefficient of an edge of the three new coordinates. -/
def triangleCoefficient
    (v : Fin (h + 3) → Fin 3 → K) (A : Fin (h + 3) → Fin 3 → Fin 3 → K)
    (ρ : Fin (h + 3 + 4) → Fin (h + 3) → K) (e : EdgeOrder.TriangleEdge) (a : Fin 3) : K :=
  ρ ((e.val.2.natAdd h).castAdd 4) (e.val.1.natAdd h) * v (e.val.1.natAdd h) a +
    ρ ((e.val.1.natAdd h).castAdd 4) (e.val.2.natAdd h) * v (e.val.2.natAdd h) a -
    A (e.val.1.natAdd h) e.val.2 a - A (e.val.2.natAdd h) e.val.1 a

private theorem newBlock (y : Fin 3 → K) (P D : Fin 3 → Fin 3 → K)
    (hD : ∀ b, D b b = 0) :
    -(∑ b, y b * ∑ c, y c * D c b) + (∑ b, y b * ∑ c, y c * P b c) =
      (∑ e : EdgeOrder.TriangleEdge, y e.val.1 * y e.val.2 *
        (P e.val.2 e.val.1 + P e.val.1 e.val.2 - D e.val.1 e.val.2 - D e.val.2 e.val.1)) +
      ∑ b, y b ^ 2 * P b b := by
  let e := Equiv.ofBijective EdgeOrder.triangleAt EdgeOrder.triangleAt_bijective
  rw [← e.sum_comp (fun p => y p.val.1 * y p.val.2 *
    (P p.val.2 p.val.1 + P p.val.1 p.val.2 - D p.val.1 p.val.2 - D p.val.2 p.val.1))]
  have h01 : e 0 = ⟨(0, 1), by decide⟩ := rfl
  have h02 : e 1 = ⟨(0, 2), by decide⟩ := rfl
  have h12 : e 2 = ⟨(1, 2), by decide⟩ := rfl
  simp only [Fin.sum_univ_three, hD, mul_zero, add_zero, zero_add, h01, h02, h12]
  ring

private theorem crossBlock (x : Fin h → K) (y : Fin 3 → K)
    (P Q D : Fin h → Fin 3 → K) :
    -(∑ b, y b * ∑ i, x i * D i b) +
      (∑ i, x i * ∑ b, y b * Q i b) +
      (∑ b, y b * ∑ i, x i * P i b) =
    ∑ i, ∑ b, x i * y b * (P i b + Q i b - D i b) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun (b : Fin 3) (i : Fin h) => y b * (x i * D i b)),
    Finset.sum_comm (f := fun (b : Fin 3) (i : Fin h) => y b * (x i * P i b))]
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Only old–new edges, the new triangle, and the three new diagonals
remain when the old coefficients and the diagonal motion terms vanish. -/
theorem base_edge_expansion
    (v : Fin (h + 3) → Fin 3 → K) (A : Fin (h + 3) → Fin 3 → Fin 3 → K)
    (ρ : Fin (h + 3 + 4) → Fin (h + 3) → K) (y : Fin (h + 3) → K) (a : Fin 3)
    (hold : ∀ i j : Fin h, ρ ((i.castAdd 3).castAdd 4) (j.castAdd 3) = 0)
    (hdiag : ∀ b : Fin 3, A (b.natAdd h) b a = 0) :
    -(∑ b : Fin 3, y (b.natAdd h) * ∑ i, y i * A i b a) +
      (∑ j : Fin (h + 3), y j * ∑ i, y i * (ρ (j.castAdd 4) i * v i a)) =
    (∑ i : Fin h, ∑ b : Fin 3, y (i.castAdd 3) * y (b.natAdd h) *
      oldNewCoefficient v A ρ i b a) +
    (∑ e : EdgeOrder.TriangleEdge, y (e.val.1.natAdd h) * y (e.val.2.natAdd h) *
      triangleCoefficient v A ρ e a) +
    ∑ b : Fin 3, y (b.natAdd h) ^ 2 * (ρ ((b.natAdd h).castAdd 4) (b.natAdd h) * v (b.natAdd h) a) := by
  have hcross := crossBlock (fun i : Fin h => y (i.castAdd 3)) (fun b : Fin 3 => y (b.natAdd h))
    (fun i b => ρ ((b.natAdd h).castAdd 4) (i.castAdd 3) * v (i.castAdd 3) a)
    (fun i b => ρ ((i.castAdd 3).castAdd 4) (b.natAdd h) * v (b.natAdd h) a)
    (fun i b => A (i.castAdd 3) b a)
  have hnew := newBlock (fun b : Fin 3 => y (b.natAdd h))
    (fun b c => ρ ((b.natAdd h).castAdd 4) (c.natAdd h) * v (c.natAdd h) a)
    (fun b c => A (b.natAdd h) c a) hdiag
  simp only [oldNewCoefficient, triangleCoefficient]
  rw [← hcross, add_assoc, ← hnew]
  simp only [Fin.sum_univ_add, hold, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
    mul_add, Finset.sum_add_distrib]
  abel

end IdealGeneration.TripleNormal.BaseEdgeExpansion
