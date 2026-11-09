module

public import IdealGeneration.ConeMonomialChart

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The middle coefficient matrix in the normal and trace monomial charts. -/

noncomputable section
namespace IdealGeneration.ConeMonomialChart
open MvPolynomial Module Matrix

variable {K : Type*} [Field K] {c m p q d : ℕ}
variable {ν τ r t o : Type*} [Fintype ν] [Fintype τ] [Fintype r] [Fintype t]

/-- The columns are normal coefficients times ambient variables, followed
by trace coefficients times normal variables. -/
abbrev MiddleColumn (c m : ℕ) (r t : Type*) := (Fin (c + m) × r) ⊕ (Fin c × t)

def shiftedCoeff {R : Type*} [CommSemiring R] {n : ℕ}
    (e u : Fin n →₀ ℕ) (j : Fin n) (a : R) : R :=
  if Finsupp.single j 1 + e = u then a else 0

theorem coeff_X_mul_monomial {n : ℕ} (e u : Fin n →₀ ℕ) (j : Fin n) (a : K) :
    (X j * monomial e a).coeff u = shiftedCoeff e u j a := by
  change (monomial (Finsupp.single j 1) 1 * monomial e a).coeff u = _
  rw [monomial_mul_monomial, one_mul, coeff_monomial]
  rfl

/-- The rows may be any selected quartic exponents. -/
def middleMatrix {R : Type*} [CommSemiring R]
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (Kn : Matrix ν r R) (Kt : Matrix τ t R) :
    Matrix o (MiddleColumn c m r t) R :=
  fun i j => Sum.elim
    (fun k => ∑ a, shiftedCoeff (en a) (out i) k.1 (Kn a k.2))
    (fun k => ∑ a, shiftedCoeff ((et a).mapDomain (Fin.natAdd c)) (out i)
      (k.1.castAdd m) (Kt a k.2)) j

omit [Fintype r] [Fintype t] in
theorem middleMatrix_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (k : R →+* S) (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (Kn : Matrix ν r R) (Kt : Matrix τ t R) :
    (middleMatrix en et out Kn Kt).map k = middleMatrix en et out (Kn.map k) (Kt.map k) := by
  ext i j
  cases j <;> simp [middleMatrix, shiftedCoeff, apply_ite]

private theorem shiftedCoeff_mulVec {n : ℕ} (e : ν → Fin n →₀ ℕ)
    (out : Fin n →₀ ℕ) (j : Fin n) (B : Matrix ν r K) (x : r → K) :
    (∑ a, shiftedCoeff (e a) out j ((B.mulVec x) a)) =
      ∑ k, (∑ a, shiftedCoeff (e a) out j (B a k)) * x k := by
  simp only [Matrix.mulVec, dotProduct, shiftedCoeff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  split <;> simp

theorem middleMatrix_mulVec (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (Kn : Matrix ν r K) (Kt : Matrix τ t K)
    (x : MiddleColumn c m r t → K) (i : o) :
    (middleMatrix en et out Kn Kt).mulVec x i =
      ((∑ j, X j * synth en (Kn.mulVec (fun k => x (.inl (j, k))))) +
        ∑ j : Fin c, X (j.castAdd m) * coneExtend K c m
          (synth et (Kt.mulVec (fun k => x (.inr (j, k)))))).coeff (out i) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [AddMonoidAlgebra.coeff_add]
  congr 1
  · rw [coeff_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (∑ k, (∑ a, shiftedCoeff (en a) (out i) j (Kn a k)) * x (.inl (j, k))) = _
    rw [synth_apply, Finset.mul_sum, coeff_sum]
    simp only [coeff_X_mul_monomial]
    exact (shiftedCoeff_mulVec en (out i) j Kn (fun k => x (.inl (j, k)))).symm
  · rw [coeff_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (∑ k, (∑ a, shiftedCoeff ((et a).mapDomain (Fin.natAdd c)) (out i)
      (j.castAdd m) (Kt a k)) * x (.inr (j, k))) = _
    rw [synth_apply, map_sum, Finset.mul_sum, coeff_sum]
    simp only [coneExtend, rename_monomial, coeff_X_mul_monomial]
    exact (shiftedCoeff_mulVec (fun a => (et a).mapDomain (Fin.natAdd c)) (out i)
      (j.castAdd m) Kt (fun k => x (.inr (j, k)))).symm

end IdealGeneration.ConeMonomialChart
