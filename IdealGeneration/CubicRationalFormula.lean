module

public import IdealGeneration.GenericMatrixDescent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Integer rational formulas and determinant denominator clearing for Appendix B.6. -/

namespace IdealGeneration.CubicRationalFormula

open MvPolynomial

/-- A rational formula with integer constants and specified inversion operations. -/
inductive Formula (ι : Type*) where
  | var : ι → Formula ι
  | integer : ℤ → Formula ι
  | add : Formula ι → Formula ι → Formula ι
  | neg : Formula ι → Formula ι
  | mul : Formula ι → Formula ι → Formula ι
  | inv : Formula ι → Formula ι
  | power : Formula ι → ℕ → Formula ι

namespace Formula

variable {ι : Type*}

instance : Add (Formula ι) := ⟨.add⟩
instance : Neg (Formula ι) := ⟨.neg⟩
instance : Mul (Formula ι) := ⟨.mul⟩
instance : Inv (Formula ι) := ⟨.inv⟩
instance : Sub (Formula ι) := ⟨fun f g => .add f (.neg g)⟩
instance : Div (Formula ι) := ⟨fun f g => .mul f (.inv g)⟩
instance : Pow (Formula ι) ℕ := ⟨.power⟩
instance : IntCast (Formula ι) := ⟨.integer⟩
instance : NatCast (Formula ι) := ⟨fun n => .integer n⟩
instance (n : ℕ) : OfNat (Formula ι) n := ⟨.integer n⟩

variable {K : Type*} [Field K]

/-- Interpret a formula using the field operations. -/
def eval : Formula ι → (ι → K) → K
  | .var i, x => x i
  | .integer z, _ => z
  | .add f g, x => f.eval x + g.eval x
  | .neg f, x => -f.eval x
  | .mul f g, x => f.eval x * g.eval x
  | .inv f, x => (f.eval x)⁻¹
  | .power f n, x => f.eval x ^ n

/-- Every syntactic inversion has a nonzero input at the assignment. -/
def Admissible : Formula ι → (ι → K) → Prop
  | .var _, _ => True
  | .integer _, _ => True
  | .add f g, x => f.Admissible x ∧ g.Admissible x
  | .neg f, x => f.Admissible x
  | .mul f g, x => f.Admissible x ∧ g.Admissible x
  | .inv f, x => f.Admissible x ∧ f.eval x ≠ 0
  | .power f _, x => f.Admissible x

@[simp] theorem eval_var (x : ι → K) (i : ι) : (Formula.var i).eval x = x i := rfl
@[simp] theorem eval_integer (x : ι → K) (z : ℤ) : (Formula.integer z).eval x = (z : K) := rfl
@[simp] theorem eval_ofNat (x : ι → K) (n : ℕ) :
    (OfNat.ofNat n : Formula ι).eval x = (n : K) := Int.cast_natCast n
@[simp] theorem eval_zero (x : ι → K) : (0 : Formula ι).eval x = 0 := Int.cast_zero
@[simp] theorem eval_one (x : ι → K) : (1 : Formula ι).eval x = 1 := Int.cast_one
@[simp] theorem eval_natCast (x : ι → K) (n : ℕ) :
    (n : Formula ι).eval x = (n : K) := Int.cast_natCast n
@[simp] theorem eval_intCast (x : ι → K) (z : ℤ) :
    (z : Formula ι).eval x = (z : K) := rfl
@[simp] theorem eval_add (x : ι → K) (f g : Formula ι) :
    (f + g).eval x = f.eval x + g.eval x := rfl
@[simp] theorem eval_neg (x : ι → K) (f : Formula ι) : (-f).eval x = -f.eval x := rfl
@[simp] theorem eval_sub (x : ι → K) (f g : Formula ι) :
    (f - g).eval x = f.eval x - g.eval x := (sub_eq_add_neg _ _).symm
@[simp] theorem eval_mul (x : ι → K) (f g : Formula ι) :
    (f * g).eval x = f.eval x * g.eval x := rfl
@[simp] theorem eval_inv (x : ι → K) (f : Formula ι) :
    (f⁻¹).eval x = (f.eval x)⁻¹ := rfl
@[simp] theorem eval_div (x : ι → K) (f g : Formula ι) :
    (f / g).eval x = f.eval x / g.eval x := (div_eq_mul_inv _ _).symm
@[simp] theorem eval_pow (x : ι → K) (f : Formula ι) (n : ℕ) :
    (f ^ n).eval x = f.eval x ^ n := rfl

/-- The formula is defined at the assignment and returns the specified value. -/
def Matches (x : ι → K) (f : Formula ι) (a : K) : Prop := f.Admissible x ∧ f.eval x = a

namespace Matches

variable {x : ι → K} {f g : Formula ι} {a b : K}

theorem var (x : ι → K) (i : ι) : Matches x (.var i) (x i) := ⟨trivial, rfl⟩
theorem integer (x : ι → K) (z : ℤ) : Matches x (.integer z) (z : K) := ⟨trivial, rfl⟩
theorem ofNat (x : ι → K) (n : ℕ) :
    Matches x (OfNat.ofNat n : Formula ι) (n : K) := ⟨trivial, eval_ofNat x n⟩
theorem natCast (x : ι → K) (n : ℕ) :
    Matches x (n : Formula ι) (n : K) := ⟨trivial, eval_natCast x n⟩
theorem intCast (x : ι → K) (z : ℤ) :
    Matches x (z : Formula ι) (z : K) := ⟨trivial, rfl⟩

theorem add (hf : Matches x f a) (hg : Matches x g b) : Matches x (f + g) (a + b) :=
  ⟨⟨hf.1, hg.1⟩, by rw [eval_add, hf.2, hg.2]⟩
theorem neg (hf : Matches x f a) : Matches x (-f) (-a) :=
  ⟨hf.1, by rw [eval_neg, hf.2]⟩
theorem sub (hf : Matches x f a) (hg : Matches x g b) : Matches x (f - g) (a - b) :=
  ⟨⟨hf.1, hg.1⟩, by rw [eval_sub, hf.2, hg.2]⟩
theorem mul (hf : Matches x f a) (hg : Matches x g b) : Matches x (f * g) (a * b) :=
  ⟨⟨hf.1, hg.1⟩, by rw [eval_mul, hf.2, hg.2]⟩
theorem inv (hf : Matches x f a) (ha : a ≠ 0) : Matches x f⁻¹ a⁻¹ :=
  ⟨⟨hf.1, hf.2 ▸ ha⟩, by rw [eval_inv, hf.2]⟩
theorem div (hf : Matches x f a) (hg : Matches x g b) (hb : b ≠ 0) :
    Matches x (f / g) (a / b) :=
  ⟨⟨hf.1, (hg.inv hb).1⟩, by rw [eval_div, hf.2, hg.2]⟩
theorem natPow (hf : Matches x f a) (n : ℕ) : Matches x (f ^ n) (a ^ n) :=
  ⟨hf.1, by rw [eval_pow, hf.2]⟩

end Matches

/-- Construct a sum in the order of a list of indices. -/
def sumList {σ : Type*} : List σ → (σ → Formula ι) → Formula ι
  | [], _ => 0
  | i :: l, f => f i + sumList l f

/-- A computable sum over a finite ordinal. -/
def sumFin {n : ℕ} (f : Fin n → Formula ι) : Formula ι := sumList (List.finRange n) f

/-- A finite-set sum uses any enumeration of the set. -/
noncomputable def sum {σ : Type*} (s : Finset σ) (f : σ → Formula ι) : Formula ι :=
  sumList s.toList f

namespace Matches

variable {x : ι → K} {σ : Type*} {f : σ → Formula ι} {y : σ → K}

theorem sumList (l : List σ) (h : ∀ i ∈ l, Matches x (f i) (y i)) :
    Matches x (Formula.sumList l f) (l.map y).sum := by
  induction l with
  | nil => exact ⟨trivial, by simp [Formula.sumList]⟩
  | cons i l ih =>
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem sumFin {n : ℕ} {f : Fin n → Formula ι} {y : Fin n → K}
    (h : ∀ i, Matches x (f i) (y i)) : Matches x (Formula.sumFin f) (∑ i, y i) := by
  simpa only [Formula.sumFin, List.finRange, List.map_ofFn, Function.comp_apply, List.sum_ofFn]
    using sumList (List.finRange n) (fun i _ => h i)

theorem sum (s : Finset σ) (h : ∀ i ∈ s, Matches x (f i) (y i)) :
    Matches x (Formula.sum s f) (∑ i ∈ s, y i) := by
  simpa only [Formula.sum, Finset.sum_map_toList]
    using sumList s.toList (fun i hi => h i (Finset.mem_toList.mp hi))

end Matches

/-- Numerator and denominator of a formula, with universal integer coefficients. -/
noncomputable def fraction : Formula ι → MvPolynomial ι ℤ × MvPolynomial ι ℤ
  | .var i => (X i, 1)
  | .integer z => (C z, 1)
  | .add f g =>
    let p := fraction f
    let q := fraction g
    (p.1 * q.2 + q.1 * p.2, p.2 * q.2)
  | .neg f => let p := fraction f; (-p.1, p.2)
  | .mul f g =>
    let p := fraction f
    let q := fraction g
    (p.1 * q.1, p.2 * q.2)
  | .inv f => (fraction f).swap
  | .power f n => let p := fraction f; (p.1 ^ n, p.2 ^ n)

noncomputable def numerator (f : Formula ι) : MvPolynomial ι ℤ := (fraction f).1
noncomputable def denominator (f : Formula ι) : MvPolynomial ι ℤ := (fraction f).2

end Formula

variable {ι : Type*} {K : Type*} [Field K]

/-- Evaluate an integer polynomial in the target field. -/
def evalPolynomial (x : ι → K) : MvPolynomial ι ℤ →+* K :=
  eval₂Hom (Int.castRingHom K) x

namespace Formula

/-- At an admissible assignment the denominator is nonzero and clearing it is exact. -/
theorem fraction_spec (f : Formula ι) (x : ι → K) (h : f.Admissible x) :
    evalPolynomial x f.denominator ≠ 0 ∧
      evalPolynomial x f.numerator = f.eval x * evalPolynomial x f.denominator := by
  induction f with
  | var i => simp [numerator, denominator, fraction, eval, evalPolynomial]
  | integer z => simp [numerator, denominator, fraction, eval, evalPolynomial]
  | add f g ihf ihg =>
    obtain ⟨hfd, hfn⟩ := ihf h.1
    obtain ⟨hgd, hgn⟩ := ihg h.2
    constructor
    · change evalPolynomial x (f.denominator * g.denominator) ≠ 0
      rw [map_mul]
      exact mul_ne_zero hfd hgd
    · change evalPolynomial x (f.numerator * g.denominator + g.numerator * f.denominator) =
        (f.eval x + g.eval x) * evalPolynomial x (f.denominator * g.denominator)
      simp only [map_add, map_mul, hfn, hgn]
      ring
  | neg f ih =>
    obtain ⟨hd, hn⟩ := ih h
    refine ⟨hd, ?_⟩
    change evalPolynomial x (-f.numerator) = -f.eval x * evalPolynomial x f.denominator
    rw [map_neg, hn, neg_mul]
  | mul f g ihf ihg =>
    obtain ⟨hfd, hfn⟩ := ihf h.1
    obtain ⟨hgd, hgn⟩ := ihg h.2
    constructor
    · change evalPolynomial x (f.denominator * g.denominator) ≠ 0
      rw [map_mul]
      exact mul_ne_zero hfd hgd
    · change evalPolynomial x (f.numerator * g.numerator) =
        f.eval x * g.eval x * evalPolynomial x (f.denominator * g.denominator)
      simp only [map_mul, hfn, hgn]
      ring
  | inv f ih =>
    obtain ⟨hd, hn⟩ := ih h.1
    constructor
    · change evalPolynomial x f.numerator ≠ 0
      rw [hn]
      exact mul_ne_zero h.2 hd
    · change evalPolynomial x f.denominator = (f.eval x)⁻¹ * evalPolynomial x f.numerator
      rw [hn, ← mul_assoc, inv_mul_cancel₀ h.2, one_mul]
  | power f n ih =>
    obtain ⟨hd, hn⟩ := ih h
    constructor
    · change evalPolynomial x (f.denominator ^ n) ≠ 0
      rw [map_pow]
      exact pow_ne_zero n hd
    · change evalPolynomial x (f.numerator ^ n) = f.eval x ^ n * evalPolynomial x (f.denominator ^ n)
      simp only [map_pow, hn, mul_pow]

theorem denominator_ne_zero (f : Formula ι) (x : ι → K) (h : f.Admissible x) :
    evalPolynomial x f.denominator ≠ 0 := (f.fraction_spec x h).1

theorem eval_eq_num_div (f : Formula ι) (x : ι → K) (h : f.Admissible x) :
    f.eval x = evalPolynomial x f.numerator / evalPolynomial x f.denominator :=
  (eq_div_iff (f.denominator_ne_zero x h)).mpr (f.fraction_spec x h).2.symm

/-- The guard retains all intermediate inversion conditions, including cancelled factors. -/
noncomputable def guard : Formula ι → MvPolynomial ι ℤ
  | .var _ => 1
  | .integer _ => 1
  | .add f g => f.guard * g.guard
  | .neg f => f.guard
  | .mul f g => f.guard * g.guard
  | .inv f => f.guard * f.numerator
  | .power f _ => f.guard

/-- The formula's guard is nonzero exactly on its admissible domain. -/
theorem eval_guard_ne_zero_iff (f : Formula ι) (x : ι → K) :
    evalPolynomial x f.guard ≠ 0 ↔ f.Admissible x := by
  induction f with
  | var i => simp [guard, Admissible]
  | integer z => simp [guard, Admissible]
  | add f g ihf ihg => simp only [guard, Admissible, map_mul, mul_ne_zero_iff, ihf, ihg]
  | neg f ih => exact ih
  | mul f g ihf ihg => simp only [guard, Admissible, map_mul, mul_ne_zero_iff, ihf, ihg]
  | inv f ih =>
    change evalPolynomial x (f.guard * f.numerator) ≠ 0 ↔ f.Admissible x ∧ f.eval x ≠ 0
    rw [map_mul, mul_ne_zero_iff, ih]
    refine and_congr_right fun h => ?_
    rw [(f.fraction_spec x h).2, mul_ne_zero_iff]
    exact and_iff_left (f.denominator_ne_zero x h)
  | power f n ih => exact ih

end Formula

section Matrix

variable {r c : Type*}

/-- Interpret a matrix of formulas entrywise. -/
def evalMatrix (x : ι → K) (A : Matrix r c (Formula ι)) : Matrix r c K :=
  fun i j => (A i j).eval x

/-- All inversions in the matrix entries are defined at the assignment. -/
def EntriesAdmissible (x : ι → K) (A : Matrix r c (Formula ι)) : Prop :=
  ∀ i j, (A i j).Admissible x

variable [Fintype c]

/-- A common denominator for one row. -/
noncomputable def rowDenominator (A : Matrix r c (Formula ι)) (i : r) : MvPolynomial ι ℤ :=
  ∏ j, (A i j).denominator

theorem eval_rowDenominator_ne_zero (x : ι → K) (A : Matrix r c (Formula ι))
    (h : EntriesAdmissible x A) (i : r) : evalPolynomial x (rowDenominator A i) ≠ 0 := by
  rw [rowDenominator, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => (A i j).denominator_ne_zero x (h i j)

variable [DecidableEq c]

/-- Each entry is multiplied by the denominators of the other entries in its row. -/
noncomputable def clearedMatrix (A : Matrix r c (Formula ι)) : Matrix r c (MvPolynomial ι ℤ) :=
  fun i j => (A i j).numerator * ∏ k ∈ Finset.univ.erase j, (A i k).denominator

/-- Evaluating the polynomial matrix scales each evaluated row by its common denominator. -/
theorem eval_clearedMatrix (x : ι → K) (A : Matrix r c (Formula ι)) (h : EntriesAdmissible x A) :
    (clearedMatrix A).map (evalPolynomial x) =
      Matrix.of fun i j => evalPolynomial x (rowDenominator A i) * evalMatrix x A i j := by
  ext i j
  change evalPolynomial x ((A i j).numerator * ∏ k ∈ Finset.univ.erase j, (A i k).denominator) =
    evalPolynomial x (∏ k, (A i k).denominator) * (A i j).eval x
  rw [map_mul, ((A i j).fraction_spec x (h i j)).2,
    ← Finset.mul_prod_erase Finset.univ (fun k => (A i k).denominator) (Finset.mem_univ j), map_mul]
  ring

/-- A polynomial determinant obtained by clearing the denominators rowwise. -/
noncomputable def matrixDeterminant (A : Matrix c c (Formula ι)) : MvPolynomial ι ℤ :=
  (clearedMatrix A).det

theorem eval_matrixDeterminant (x : ι → K) (A : Matrix c c (Formula ι))
    (h : EntriesAdmissible x A) :
    evalPolynomial x (matrixDeterminant A) =
      (∏ i, evalPolynomial x (rowDenominator A i)) * (evalMatrix x A).det := by
  rw [matrixDeterminant, RingHom.map_det]
  change ((clearedMatrix A).map (evalPolynomial x)).det = _
  rw [eval_clearedMatrix x A h, Matrix.det_mul_column]

/-- Under entry admissibility the polynomial determinant detects nonsingularity exactly. -/
theorem eval_matrixDeterminant_ne_zero_iff (x : ι → K) (A : Matrix c c (Formula ι))
    (h : EntriesAdmissible x A) :
    evalPolynomial x (matrixDeterminant A) ≠ 0 ↔ (evalMatrix x A).det ≠ 0 := by
  rw [eval_matrixDeterminant x A h, mul_ne_zero_iff]
  exact and_iff_right (Finset.prod_ne_zero_iff.mpr fun i _ => eval_rowDenominator_ne_zero x A h i)

/-- The product of entry guards and the cleared determinant imposes both conditions. -/
noncomputable def matrixCertificate (A : Matrix c c (Formula ι)) : MvPolynomial ι ℤ :=
  (∏ i, ∏ j, (A i j).guard) * matrixDeterminant A

/-- One polynomial detects the defined and nonsingular assignments. -/
theorem eval_matrixCertificate_ne_zero_iff (x : ι → K) (A : Matrix c c (Formula ι)) :
    evalPolynomial x (matrixCertificate A) ≠ 0 ↔
      EntriesAdmissible x A ∧ (evalMatrix x A).det ≠ 0 := by
  have hg : evalPolynomial x (∏ i, ∏ j, (A i j).guard) ≠ 0 ↔ EntriesAdmissible x A := by
    simp only [EntriesAdmissible, map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies,
      Formula.eval_guard_ne_zero_iff]
  rw [matrixCertificate, map_mul, mul_ne_zero_iff, hg]
  exact and_congr_right fun h => eval_matrixDeterminant_ne_zero_iff x A h

/-- Any field witness proves that the universal certificate polynomial is nonzero. -/
theorem matrixCertificate_ne_zero_of_eval (x : ι → K) (A : Matrix c c (Formula ι))
    (h : EntriesAdmissible x A) (hne : (evalMatrix x A).det ≠ 0) : matrixCertificate A ≠ 0 := by
  intro hz
  exact (eval_matrixCertificate_ne_zero_iff x A).mpr ⟨h, hne⟩ (by rw [hz, map_zero])

/-- A field witness, including a finite-field witness, yields a characteristic-zero polynomial. -/
theorem map_matrixCertificate_ne_zero_of_eval {L : Type*} [Field L] [CharZero L]
    (x : ι → K) (A : Matrix c c (Formula ι)) (h : EntriesAdmissible x A)
    (hne : (evalMatrix x A).det ≠ 0) :
    MvPolynomial.map (Int.castRingHom L) (matrixCertificate A) ≠ 0 := by
  have hinj : Function.Injective (MvPolynomial.map (σ := ι) (Int.castRingHom L)) :=
    MvPolynomial.map_injective _ Int.cast_injective
  simpa only [map_zero] using hinj.ne (matrixCertificate_ne_zero_of_eval x A h hne)

/-- Pointwise matching identifies the matrix whose determinant is tested. -/
theorem eval_matrixCertificate_ne_zero_iff_of_matches (x : ι → K)
    (A : Matrix c c (Formula ι)) (B : Matrix c c K)
    (h : ∀ i j, Formula.Matches x (A i j) (B i j)) :
    evalPolynomial x (matrixCertificate A) ≠ 0 ↔ B.det ≠ 0 := by
  have hadm : EntriesAdmissible x A := fun i j => (h i j).1
  have hB : evalMatrix x A = B := Matrix.ext fun i j => (h i j).2
  rw [eval_matrixCertificate_ne_zero_iff x A, hB]
  exact and_iff_right hadm

/-- A nonsingular admissible witness over any field descends to characteristic zero. -/
theorem matrixCertificate_descends {L : Type*} [Field L] [CharZero L]
    (x : ι → K) (A : Matrix c c (Formula ι)) (h : EntriesAdmissible x A)
    (hne : (evalMatrix x A).det ≠ 0) :
    ∃ y : ι → L, EntriesAdmissible y A ∧ (evalMatrix y A).det ≠ 0 := by
  have hw := (eval_matrixCertificate_ne_zero_iff x A).mpr ⟨h, hne⟩
  obtain ⟨y, hy⟩ := integer_polynomial_nonvanishing_descends (K := L) (matrixCertificate A) x hw
  exact ⟨y, (eval_matrixCertificate_ne_zero_iff y A).mp hy⟩

end Matrix
end IdealGeneration.CubicRationalFormula
