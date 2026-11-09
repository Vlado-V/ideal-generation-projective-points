module

public import IdealGeneration.Homogeneous

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The polynomial injection in the two-normal quadratic construction

The base variables are indexed by `I`, and arbitrary additional layers by `J`.
The two components of the `i`th mixed generator restrict to `(y_i,c_i y_i)`
on the base. All additional terms involve layer variables. Distinct `c_i`
make multiplication by linear forms injective for any number of layers and
any values of those layer corrections.
-/

noncomputable section
namespace IdealGeneration.QuadraticFlag
open MvPolynomial Module

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

/-- A coefficient vector represented by its genuine linear polynomial. -/
def linearPolynomial {V : Type*} [Fintype V] (a : V → K) : MvPolynomial V K :=
  ∑ v, C (a v) * X v

@[simp] theorem eval_linearPolynomial {V : Type*} [Fintype V]
    (a x : V → K) :
    eval x (linearPolynomial a) = ∑ v, a v * x v := by
  simp [linearPolynomial]

/-- A coordinate vector, also used as an affine representative of a projective point. -/
def coordinatePoint {V : Type*} [DecidableEq V] (v : V) : V → K :=
  fun w => if w = v then 1 else 0

@[simp] theorem eval_linearPolynomial_coordinate {V : Type*} [Fintype V]
    [DecidableEq V] (a : V → K) (v : V) :
    eval (coordinatePoint v) (linearPolynomial a) = a v := by
  simp [coordinatePoint]

@[simp] theorem eval_linearPolynomial_add {V : Type*} [Fintype V]
    (a x y : V → K) :
    eval (x + y) (linearPolynomial a) =
      eval x (linearPolynomial a) + eval y (linearPolynomial a) := by
  simp [mul_add, Finset.sum_add_distrib]

/-- The first component of a mixed generator, including arbitrary layer terms. -/
def firstGenerator (a : I → J → K) (i : I) : MvPolynomial (I ⊕ J) K :=
  X (Sum.inl i) + ∑ j, C (a i j) * X (Sum.inr j)

/-- The second component of a mixed generator, including arbitrary layer terms. -/
def secondGenerator (c : I → K) (b : I → J → K) (i : I) :
    MvPolynomial (I ⊕ J) K :=
  C (c i) * X (Sum.inl i) + ∑ j, C (b i j) * X (Sum.inr j)

/-- Multiplication of the mixed generators by independent linear forms. -/
def multiplication (c : I → K) (a b : I → J → K) :
    (I → I ⊕ J → K) →ₗ[K]
      (MvPolynomial (I ⊕ J) K × MvPolynomial (I ⊕ J) K) where
  toFun L := (∑ i, firstGenerator a i * linearPolynomial (L i),
    ∑ i, secondGenerator c b i * linearPolynomial (L i))
  map_add' L M := by
    apply Prod.ext <;>
      simp [linearPolynomial, Pi.add_apply, map_add, add_mul, mul_add,
        Finset.sum_add_distrib]
  map_smul' r L := by
    have hlin (i : I) : linearPolynomial ((r • L) i) = r • linearPolynomial (L i) := by
      simp only [linearPolynomial, Pi.smul_apply, smul_eq_mul, map_mul,
        Algebra.smul_def, MvPolynomial.algebraMap_eq, Finset.mul_sum, mul_assoc]
    apply Prod.ext <;>
      simp only [hlin, Prod.smul_mk, Finset.smul_sum, mul_smul_comm, RingHom.id_apply]

/-- Every coefficient vector represents a homogeneous linear form. -/
theorem linearPolynomial_isHomogeneous {V : Type*} [Fintype V] (a : V → K) :
    (linearPolynomial a).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- The image consists of pairs of homogeneous quadratic forms. -/
theorem multiplication_isHomogeneous (c : I → K) (a b : I → J → K)
    (L : I → I ⊕ J → K) :
    ((multiplication c a b L).1).IsHomogeneous 2 ∧
      ((multiplication c a b L).2).IsHomogeneous 2 := by
  have first (i : I) : (firstGenerator a i).IsHomogeneous 1 := by
    apply (MvPolynomial.isHomogeneous_X K (Sum.inl i)).add
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  have second (i : I) : (secondGenerator c b i).IsHomogeneous 1 := by
    apply (MvPolynomial.isHomogeneous_C_mul_X (c i) (Sum.inl i)).add
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  constructor
  · exact MvPolynomial.IsHomogeneous.sum _ _ _
      (fun i _ => (first i).mul (linearPolynomial_isHomogeneous (L i)))
  · exact MvPolynomial.IsHomogeneous.sum _ _ _
      (fun i _ => (second i).mul (linearPolynomial_isHomogeneous (L i)))

/-- The two polynomial identities force all linear coefficients to vanish.
The proof uses their values on coordinate points and sums of two coordinate points. -/
theorem multiplication_eq_zero (c : I → K) (a b : I → J → K)
    (hc : Function.Injective c) (L : I → I ⊕ J → K)
    (hL : multiplication c a b L = 0) : L = 0 := by
  classical
  have hfst : ∑ i, firstGenerator a i * linearPolynomial (L i) = 0 :=
    congrArg Prod.fst hL
  have hsnd : ∑ i, secondGenerator c b i * linearPolynomial (L i) = 0 :=
    congrArg Prod.snd hL
  have diag (i : I) : L i (.inl i) = 0 := by
    have h := congrArg (eval (coordinatePoint (Sum.inl i))) hfst
    simpa [firstGenerator, coordinatePoint] using h
  have off (i k : I) : L i (.inl k) = 0 := by
    by_cases hik : i = k
    · subst k
      exact diag i
    have hp : L i (.inl k) + L k (.inl i) = 0 := by
      have h := congrArg (eval (coordinatePoint (Sum.inl i) +
        coordinatePoint (Sum.inl k))) hfst
      simp [firstGenerator, coordinatePoint, mul_add, add_mul,
        Finset.sum_add_distrib, diag] at h
      simpa only [add_comm] using h
    have hq : c i * L i (.inl k) + c k * L k (.inl i) = 0 := by
      have h := congrArg (eval (coordinatePoint (Sum.inl i) +
        coordinatePoint (Sum.inl k))) hsnd
      simp [secondGenerator, coordinatePoint, mul_add, add_mul,
        Finset.sum_add_distrib, diag] at h
      simpa only [add_comm] using h
    have hci : c i - c k ≠ 0 := sub_ne_zero.mpr (fun he => hik (hc he))
    have hm : (c i - c k) * L i (.inl k) = 0 := by
      linear_combination hq - c k * hp
    exact (mul_eq_zero.mp hm).resolve_left hci
  have layer (i : I) (j : J) : L i (.inr j) = 0 := by
    have hbase := congrArg (eval (coordinatePoint (Sum.inr j))) hfst
    have hmix := congrArg (eval (coordinatePoint (Sum.inl i) +
      coordinatePoint (Sum.inr j))) hfst
    simp [firstGenerator, coordinatePoint, off, mul_add, add_mul,
      Finset.sum_add_distrib] at hbase hmix
    linear_combination hmix - hbase
  funext i v
  cases v with
  | inl k => exact off i k
  | inr j => exact layer i j

/-- The injection used in Appendix A.2 holds uniformly for every finite number of layers. -/
theorem multiplication_injective (c : I → K) (a b : I → J → K)
    (hc : Function.Injective c) : Function.Injective (multiplication c a b) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro L hL
  exact multiplication_eq_zero c a b hc L hL

/-- The space `U` generated by the mixed generators times trace-linear forms. -/
def mixedImage (c : I → K) (a b : I → J → K) :
    Submodule K (MvPolynomial (I ⊕ J) K × MvPolynomial (I ⊕ J) K) :=
  (multiplication c a b).range

/-- Its dimension is `h*m`, where `h` is the number of base variables and
`m=h+l` is the total number of trace variables. -/
theorem finrank_mixedImage (c : I → K) (a b : I → J → K)
    (hc : Function.Injective c) :
    finrank K (mixedImage c a b) = Fintype.card I * (Fintype.card I + Fintype.card J) := by
  rw [mixedImage, LinearMap.finrank_range_of_inj (multiplication_injective c a b hc)]
  simp [Module.finrank_pi_fintype, Fintype.card_sum]

end IdealGeneration.QuadraticFlag
