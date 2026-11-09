module

public import IdealGeneration.TripleNormalBaseEvaluation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The coefficient map tested at the free points of the enlarged base. -/

noncomputable section
namespace IdealGeneration.TripleNormal

variable {K : Type*} [Field K] {h r : ℕ}

/-- The base value of a new motion and its mixed-product coefficients. -/
def newBaseValue (ω : K) (t : Fin h → K) (v : Fin 3 → K)
    (u : Fin 3 → Fin 3 → K) (ρ : Fin (h + 3 + 4) → Fin (h + 3) → K)
    (y : Fin (h + 3) → K) (a : Fin 3) : K :=
  -(∑ b : Fin 3, y (b.natAdd h) *
    ∑ i, y i * baseLiftCoefficient ω (Fin.append t v i) (newMotionQuadric v u b) a) +
    ∑ j : Fin (h + 3), y j *
      ∑ i, y i * (ρ (j.castAdd 4) i * conicVector (Fin.append t v i) a)

/-- The free base rows detect all motions and remaining base products after
the old and diagonal coefficients have vanished. -/
def NewBaseRank (ω : K) (t : Fin h → K) (v : Fin 3 → K)
    (free : Fin r × Fin (h + 3) → K) : Prop :=
  ∀ (u : Fin 3 → Fin 3 → K) (ρ : Fin (h + 3 + 4) → Fin (h + 3) → K),
    (∀ i j : Fin h, ρ ((i.castAdd 3).castAdd 4) (j.castAdd 3) = 0) →
    (∀ b : Fin 3, ρ ((b.natAdd h).castAdd 4) (b.natAdd h) = 0) →
    (∀ i : Fin r, ∀ a : Fin 3, newBaseValue ω t v u ρ (fun j => free (i, j)) a = 0) →
    u = 0 ∧ ∀ j : Fin (h + 3), ρ (j.castAdd 4) = 0

end IdealGeneration.TripleNormal
