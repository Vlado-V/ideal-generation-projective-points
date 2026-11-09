module

public import IdealGeneration.ConeMiddleMatrix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Joint evaluation and multiplication on the fixed monomial-coordinate spaces. -/

noncomputable section
namespace IdealGeneration.ConeMonomialChart
open MvPolynomial Matrix

variable {K : Type*} [Field K] {c m p q : ℕ}
variable {ν τ r t o : Type*} [Fintype ν] [Fintype τ] [Fintype r] [Fintype t]

abbrev EvaluationRow (c m p q : ℕ) := (Fin (c + m) × Fin p) ⊕ (Fin c × Fin q)

/-- Impose the normal and trace evaluation equations separately on each variable. -/
def jointEvaluation {R : Type*} [CommSemiring R]
    (En : Matrix (Fin p) ν R) (Et : Matrix (Fin q) τ R) :
    Matrix (EvaluationRow c m p q) (MiddleColumn c m ν τ) R
  | .inl i, .inl j => if i.1 = j.1 then En i.2 j.2 else 0
  | .inr i, .inr j => if i.1 = j.1 then Et i.2 j.2 else 0
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0

theorem jointEvaluation_mulVec_normal
    (En : Matrix (Fin p) ν K) (Et : Matrix (Fin q) τ K)
    (x : MiddleColumn c m ν τ → K) (j : Fin (c + m)) (i : Fin p) :
    (jointEvaluation En Et).mulVec x (.inl (j, i)) =
      En.mulVec (fun a => x (.inl (j, a))) i := by
  classical
  simp [jointEvaluation, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_prod_type, ite_mul, Finset.sum_ite_eq]

theorem jointEvaluation_mulVec_trace
    (En : Matrix (Fin p) ν K) (Et : Matrix (Fin q) τ K)
    (x : MiddleColumn c m ν τ → K) (j : Fin c) (i : Fin q) :
    (jointEvaluation En Et).mulVec x (.inr (j, i)) =
      Et.mulVec (fun a => x (.inr (j, a))) i := by
  classical
  simp [jointEvaluation, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_prod_type, ite_mul, Finset.sum_ite_eq]

omit [Fintype ν] [Fintype τ] in
theorem jointEvaluation_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (k : R →+* S) (En : Matrix (Fin p) ν R) (Et : Matrix (Fin q) τ R) :
    (jointEvaluation (c := c) (m := m) En Et).map k =
      jointEvaluation (En.map k) (Et.map k) := by
  ext i j
  cases i <;> cases j <;> simp only [jointEvaluation, Matrix.map_apply, apply_ite, map_zero]
  all_goals split <;> simp_all

variable [DecidableEq ν] [DecidableEq τ]

/-- The coefficient stack encodes absence of a relation in the two evaluation kernels. -/
def jointMatrix {R : Type*} [CommSemiring R]
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (En : Matrix (Fin p) ν R) (Et : Matrix (Fin q) τ R) :
    Matrix (EvaluationRow c m p q ⊕ o) (MiddleColumn c m ν τ) R :=
  Sum.elim (jointEvaluation En Et)
    (middleMatrix en et out (1 : Matrix ν ν R) (1 : Matrix τ τ R))

theorem jointMatrix_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (k : R →+* S) (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (En : Matrix (Fin p) ν R) (Et : Matrix (Fin q) τ R) :
    (jointMatrix en et out En Et).map k = jointMatrix en et out (En.map k) (Et.map k) := by
  ext i j
  cases i with
  | inl i => exact congrFun (congrFun (jointEvaluation_map (c := c) (m := m) k En Et) i) j
  | inr i =>
    have h := middleMatrix_map k en et out (1 : Matrix ν ν R) (1 : Matrix τ τ R)
    rw [Matrix.map_one _ (map_zero k) (map_one k), Matrix.map_one _ (map_zero k) (map_one k)] at h
    exact congrFun (congrFun h i) j

private theorem jointMatrix_mulVec_normal
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (En : Matrix (Fin p) ν K) (Et : Matrix (Fin q) τ K)
    (x : MiddleColumn c m ν τ → K) (j : Fin (c + m)) (i : Fin p) :
    (jointMatrix en et out En Et).mulVec x (.inl (.inl (j, i))) =
      En.mulVec (fun a => x (.inl (j, a))) i :=
  jointEvaluation_mulVec_normal En Et x j i

private theorem jointMatrix_mulVec_trace
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (En : Matrix (Fin p) ν K) (Et : Matrix (Fin q) τ K)
    (x : MiddleColumn c m ν τ → K) (j : Fin c) (i : Fin q) :
    (jointMatrix en et out En Et).mulVec x (.inl (.inr (j, i))) =
      Et.mulVec (fun a => x (.inr (j, a))) i :=
  jointEvaluation_mulVec_trace En Et x j i

/-- A coefficient-kernel chart and an injective middle minor certify the stack. -/
theorem jointMatrix_injective_of_kernel_columns
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (En : Matrix (Fin p) ν K) (Et : Matrix (Fin q) τ K)
    (Kn : Matrix ν r K) (Kt : Matrix τ t K)
    (hnk : ∀ u, En.mulVec u = 0 → ∃ v, Kn.mulVec v = u)
    (htk : ∀ u, Et.mulVec u = 0 → ∃ v, Kt.mulVec v = u)
    (hm : Function.Injective (middleMatrix en et out Kn Kt).mulVec) :
    Function.Injective (jointMatrix en et out En Et).mulVec := by
  let A := jointMatrix en et out En Et
  suffices hz : ∀ x, A.mulVec x = 0 → x = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [Matrix.mulVec_sub, hxy, sub_self]
  intro x hx
  change (jointMatrix en et out En Et).mulVec x = 0 at hx
  have hn : ∀ j : Fin (c + m), ∃ v, Kn.mulVec v = fun a => x (.inl (j, a)) := by
    intro j
    apply hnk
    funext i
    simpa only [jointMatrix_mulVec_normal, Pi.zero_apply] using congrFun hx (.inl (.inl (j, i)))
  have ht : ∀ j : Fin c, ∃ v, Kt.mulVec v = fun a => x (.inr (j, a)) := by
    intro j
    apply htk
    funext i
    simpa only [jointMatrix_mulVec_trace, Pi.zero_apply] using congrFun hx (.inl (.inr (j, i)))
  choose xn hxn using hn
  choose xt hxt using ht
  let y : MiddleColumn c m r t → K := Sum.elim (fun j => xn j.1 j.2) (fun j => xt j.1 j.2)
  have hMy : (middleMatrix en et out Kn Kt).mulVec y = 0 := by
    funext i
    have hi := congrFun hx (.inr i)
    change (middleMatrix en et out (1 : Matrix ν ν K) (1 : Matrix τ τ K)).mulVec x i = 0 at hi
    rw [middleMatrix_mulVec] at hi ⊢
    simpa only [y, Sum.elim_inl, Sum.elim_inr, hxn, hxt, Matrix.one_mulVec, Pi.zero_apply] using hi
  have hy : y = 0 := hm (hMy.trans (Matrix.mulVec_zero _).symm)
  funext a
  cases a with
  | inl a =>
    have hj : xn a.1 = 0 := funext fun k => congrFun hy (.inl (a.1, k))
    simpa only [hj, Matrix.mulVec_zero, Pi.zero_apply] using congrFun (hxn a.1).symm a.2
  | inr a =>
    have hj : xt a.1 = 0 := funext fun k => congrFun hy (.inr (a.1, k))
    simpa only [hj, Matrix.mulVec_zero, Pi.zero_apply] using congrFun (hxt a.1).symm a.2

/-- Injectivity of the coefficient stack implies injectivity of the native
middle map at the same actual representatives. -/
theorem middle_injective_of_jointMatrix {d : ℕ}
    (C : ConeConfiguration K c m p q)
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ)
    (hnd : ∀ i, (en i).degree = d) (htd : ∀ i, (et i).degree = d)
    (hnn : ∀ i, ∃ j : Fin c, en i (j.castAdd m) ≠ 0)
    (hns : Function.Surjective (normalSynth (K := K) en hnd hnn))
    (hts : Function.Surjective (formSynth (K := K) et htd))
    (hm : Function.Injective
      (jointMatrix en et out (evaluationMatrix C.point en) (evaluationMatrix C.trace et)).mulVec) :
    Function.Injective (C.middleMultiplication d) := by
  suffices hzero : ∀ f, C.middleMultiplication d f = 0 → f = 0 by
    intro f g h
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, h, sub_self]
  intro f hf
  have hn : ∀ j : Fin (c + m), ∃ u, synth en u = (f.1 j).val.val := by
    intro j
    obtain ⟨u, hu⟩ := hns ⟨(f.1 j).val, (f.1 j).property.2⟩
    exact ⟨u, congrArg (fun g => g.val.val) hu⟩
  have ht : ∀ j : Fin c, ∃ u, synth et u = (f.2 j).val.val := by
    intro j
    obtain ⟨u, hu⟩ := hts (f.2 j).val
    exact ⟨u, congrArg Subtype.val hu⟩
  choose xn hxn using hn
  choose xt hxt using ht
  let x : MiddleColumn c m ν τ → K := Sum.elim (fun j => xn j.1 j.2) (fun j => xt j.1 j.2)
  have hprod :
      (jointMatrix en et out (evaluationMatrix C.point en) (evaluationMatrix C.trace et)).mulVec x =
        0 := by
    funext i
    cases i with
    | inl i =>
      cases i with
      | inl a =>
        rw [jointMatrix_mulVec_normal, Pi.zero_apply]
        change (∑ b, (∏ k, C.point a.2 k ^ en b k) * xn a.1 b) = 0
        rw [← evaluationMatrix_mulVec, hxn]
        exact (C.mem_conePiece _).mp (f.1 a.1).property.1 a.2
      | inr a =>
        rw [jointMatrix_mulVec_trace, Pi.zero_apply]
        change (∑ b, (∏ k, C.trace a.2 k ^ et b k) * xt a.1 b) = 0
        rw [← evaluationMatrix_mulVec, hxt]
        exact (C.mem_tracePiece _).mp (f.2 a.1).property a.2
    | inr i =>
      change (middleMatrix en et out (1 : Matrix ν ν K) (1 : Matrix τ τ K)).mulVec x i = 0
      rw [middleMatrix_mulVec]
      simp only [x, Sum.elim_inl, Sum.elim_inr, Matrix.one_mulVec, hxn, hxt]
      have hp := congrArg (fun z => z.val.val) hf
      rw [C.middleMultiplication_val] at hp
      simp only [Submodule.coe_add, formMultiplication_val] at hp
      have htail : (∑ j : Fin (c + m), X j * (C.normalTraceCoefficients d f.2 j).val) =
          ∑ j : Fin c, X (j.castAdd m) * coneExtend K c m (f.2 j).val.val := by
        rw [Fin.sum_univ_add]
        simp [ConeConfiguration.normalTraceCoefficients, coneExtendForm]
      rw [htail] at hp
      rw [hp]
      rfl
  have hx : x = 0 := hm (hprod.trans (Matrix.mulVec_zero _).symm)
  apply Prod.ext
  · funext j
    apply Subtype.ext
    apply Subtype.ext
    have hj : xn j = 0 := funext (fun k => congrFun hx (.inl (j, k)))
    simpa [hj] using (hxn j).symm
  · funext j
    apply Subtype.ext
    apply Subtype.ext
    have hj : xt j = 0 := funext (fun k => congrFun hx (.inr (j, k)))
    simpa [hj] using (hxt j).symm

end IdealGeneration.ConeMonomialChart
