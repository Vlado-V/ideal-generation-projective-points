module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Separation by normal degree

The two normal variables form a polynomial ring over an arbitrary
commutative coefficient ring. Its monomial coefficients separate the
normal-linear part from all terms of normal degree two and three.
-/

noncomputable section

namespace IdealGeneration.QuadraticNormalCoefficients
open MvPolynomial AddMonoidAlgebra

/-- The bidegree of a monomial in the two normal variables. -/
def normalExponent (p q : ℕ) : Bool →₀ ℕ :=
  Finsupp.single false p + Finsupp.single true q

@[simp] theorem normalExponent_false (p q : ℕ) : normalExponent p q false = p := by
  simp [normalExponent]

@[simp] theorem normalExponent_true (p q : ℕ) : normalExponent p q true = q := by
  simp [normalExponent]

@[simp] theorem normalExponent_eq_iff (p q r s : ℕ) :
    normalExponent p q = normalExponent r s ↔ p = r ∧ q = s := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun e : Bool →₀ ℕ => e false) h,
      by simpa using congrArg (fun e : Bool →₀ ℕ => e true) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

variable {R : Type*} [CommRing R]

/-- A normal monomial with a coefficient in the trace ring. -/
def normalMonomial (p q : ℕ) (r : R) : MvPolynomial Bool R :=
  monomial (normalExponent p q) r

/-- The monomial representation agrees with the ordinary product notation. -/
theorem normalMonomial_eq (p q : ℕ) (r : R) :
    normalMonomial p q r = C r * X false ^ p * X true ^ q := by
  symm
  rw [C_mul_X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  rfl

@[simp] theorem coeff_normalMonomial (p q i j : ℕ) (r : R) :
    coeff (normalMonomial p q r) (normalExponent i j) =
      if p = i ∧ q = j then r else 0 := by
  simp only [normalMonomial, coeff_monomial, normalExponent_eq_iff]

/-- If a polynomial of normal degrees one, two, and three is normal-linear,
all seven higher-degree coefficients vanish, and its linear coefficients
are uniquely determined. The coefficient ring need not be a field. -/
theorem normalDegree_separation (a b c d u v w A B A' B' : R)
    (h : C a * X false ^ 3 + C b * X false ^ 2 * X true +
      C c * X false * X true ^ 2 + C d * X true ^ 3 +
      C u * X false ^ 2 + C v * X false * X true + C w * X true ^ 2 +
      C A * X false + C B * X true =
      C A' * X false + C B' * X true) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ u = 0 ∧ v = 0 ∧ w = 0 ∧ A = A' ∧ B = B' := by
  have hm : normalMonomial 3 0 a + normalMonomial 2 1 b + normalMonomial 1 2 c +
      normalMonomial 0 3 d + normalMonomial 2 0 u + normalMonomial 1 1 v +
      normalMonomial 0 2 w + normalMonomial 1 0 A + normalMonomial 0 1 B =
      normalMonomial 1 0 A' + normalMonomial 0 1 B' := by
    simpa only [normalMonomial_eq, pow_zero, pow_one, mul_one] using h
  have ha : a = 0 := by
    simpa using congrArg (fun f => coeff f (normalExponent 3 0)) hm
  have hb : b = 0 := by
    simpa using congrArg (fun f => coeff f (normalExponent 2 1)) hm
  have hc : c = 0 := by
    simpa using congrArg (fun f => coeff f (normalExponent 1 2)) hm
  have hd : d = 0 := by
    simpa using congrArg (fun f => coeff f (normalExponent 0 3)) hm
  have hu : u = 0 := by
    simpa using congrArg (fun f => coeff f (normalExponent 2 0)) hm
  have hv : v = 0 := by
    simpa using congrArg (fun f => coeff f (normalExponent 1 1)) hm
  have hw : w = 0 := by
    simpa using congrArg (fun f => coeff f (normalExponent 0 2)) hm
  have hA : A = A' := by
    simpa using congrArg (fun f => coeff f (normalExponent 1 0)) hm
  have hB : B = B' := by
    simpa using congrArg (fun f => coeff f (normalExponent 0 1)) hm
  exact ⟨ha, hb, hc, hd, hu, hv, hw, hA, hB⟩

end IdealGeneration.QuadraticNormalCoefficients
