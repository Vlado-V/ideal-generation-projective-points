module

public import IdealGeneration.Points

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# A common affine chart for finitely many nonzero representatives

The last coordinate can be changed by a shear so that it is nonzero on every
representative. The existence proof is polynomial avoidance over an infinite field.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable {K : Type*} [Field K] [Infinite K]

/-- Finitely many nonzero projective representatives admit a common affine chart
whose defining linear form has final coefficient one. -/
theorem exists_shear_avoiding_representatives {n p : ℕ}
    (z : Fin p → Fin (n + 1) → K) (hz : ∀ i, z i ≠ 0) :
    ∃ v : Fin n → K, ∀ i,
      z i (Fin.last n) + ∑ j, v j * z i j.castSucc ≠ 0 := by
  classical
  let L : Fin p → MvPolynomial (Fin n) K := fun i =>
    C (z i (Fin.last n)) + ∑ j, C (z i j.castSucc) * X j
  have hL : ∀ i, L i ≠ 0 := by
    intro i heq
    have hlast : z i (Fin.last n) = 0 := by
      have heval := congrArg (MvPolynomial.eval (0 : Fin n → K)) heq
      simpa [L] using heval
    have hcast : ∀ j : Fin n, z i j.castSucc = 0 := by
      intro j
      have heval := congrArg (MvPolynomial.eval (Pi.single j 1)) heq
      simpa [L, hlast, Pi.single_apply, mul_ite] using heval
    apply hz i
    funext j
    exact Fin.lastCases hlast hcast j
  have hprod : (∏ i, L i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hL i)
  have hex : ∃ v : Fin n → K, MvPolynomial.eval v (∏ i, L i) ≠ 0 := by
    by_contra! h
    apply hprod
    apply MvPolynomial.funext
    intro v
    simpa using h v
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, fun i => ?_⟩
  have hi : MvPolynomial.eval v (L i) ≠ 0 := by
    have h := (Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hv))
    exact h i (Finset.mem_univ i)
  simpa [L, mul_comm] using hi

end IdealGeneration
