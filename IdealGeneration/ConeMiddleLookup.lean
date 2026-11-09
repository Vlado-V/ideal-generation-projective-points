module

public import IdealGeneration.ConeMiddleMatrix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! A verified predecessor lookup evaluates one coefficient without a monomial sum. -/

namespace IdealGeneration.ConeMonomialChart
open Matrix

variable {R : Type*} [CommSemiring R] {c m : ℕ}
variable {ν τ r t o : Type*} [Fintype ν] [Fintype τ]

private theorem sum_shiftedCoeff_of_lookup {n : ℕ}
    (e : ν → Fin n →₀ ℕ) (u : Fin n →₀ ℕ) (j : Fin n) (f : ν → R)
    (look : Option ν)
    (h : ∀ a, Finsupp.single j 1 + e a = u ↔ look = some a) :
    ∑ a, shiftedCoeff (e a) u j (f a) = (look.map f).getD 0 := by
  classical
  simp only [shiftedCoeff, h]
  cases look with
  | none => simp
  | some a => simp [Finset.sum_ite_eq]

theorem middleMatrix_apply_inl_of_lookup
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (Kn : Matrix ν r R) (Kt : Matrix τ t R)
    (i : o) (j : Fin (c + m)) (k : r) (look : Option ν)
    (h : ∀ a, Finsupp.single j 1 + en a = out i ↔ look = some a) :
    middleMatrix en et out Kn Kt i (.inl (j, k)) =
      (look.map (fun a => Kn a k)).getD 0 :=
  sum_shiftedCoeff_of_lookup en (out i) j (fun a => Kn a k) look h

theorem middleMatrix_apply_inr_of_lookup
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (Kn : Matrix ν r R) (Kt : Matrix τ t R)
    (i : o) (j : Fin c) (k : t) (look : Option τ)
    (h : ∀ a, Finsupp.single (j.castAdd m) 1 + (et a).mapDomain (Fin.natAdd c) = out i ↔
      look = some a) :
    middleMatrix en et out Kn Kt i (.inr (j, k)) =
      (look.map (fun a => Kt a k)).getD 0 :=
  sum_shiftedCoeff_of_lookup (fun a => (et a).mapDomain (Fin.natAdd c)) (out i)
    (j.castAdd m) (fun a => Kt a k) look h

end IdealGeneration.ConeMonomialChart
