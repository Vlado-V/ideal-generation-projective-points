module

public import IdealGeneration.QuadraticFlag

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Coefficient vectors and homogeneous linear polynomials

The coefficient-vector model used in the quadratic construction describes
every genuine homogeneous linear polynomial. Its coefficients are recovered
by evaluation at the coordinate points.
-/

noncomputable section
namespace IdealGeneration.QuadraticFlag
open MvPolynomial

variable {K T : Type*} [Field K] [Fintype T]

/-- Realize a coefficient vector as its homogeneous linear polynomial. -/
def linearPolynomialLinearMap : (T → K) →ₗ[K] MvPolynomial T K where
  toFun := linearPolynomial
  map_add' a b := by
    simp [linearPolynomial, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [linearPolynomial, Pi.smul_apply, smul_eq_mul, map_mul,
      Algebra.smul_def, MvPolynomial.algebraMap_eq, Finset.mul_sum, mul_assoc,
      RingHom.id_apply]

@[simp] theorem linearPolynomialLinearMap_apply (a : T → K) :
    linearPolynomialLinearMap a = linearPolynomial a := rfl

/-- Coordinate evaluation recovers every coefficient, so the realization is injective. -/
theorem linearPolynomialLinearMap_injective :
    Function.Injective (linearPolynomialLinearMap (K := K) (T := T)) := by
  classical
  intro a b hab
  funext i
  have h := congrArg (eval (coordinatePoint i)) hab
  change eval (coordinatePoint i) (linearPolynomial a) =
    eval (coordinatePoint i) (linearPolynomial b) at h
  simpa only [eval_linearPolynomial_coordinate] using h

/-- Coordinate vectors realize the individual variables. -/
@[simp] theorem linearPolynomial_coordinatePoint [DecidableEq T] (i : T) :
    linearPolynomial (coordinatePoint (K := K) i) = X i := by
  simp [linearPolynomial, coordinatePoint]

/-- The image of coefficient realization is exactly the homogeneous degree-one space. -/
theorem linearPolynomialLinearMap_range :
    (linearPolynomialLinearMap (K := K) (T := T)).range =
      homogeneousSubmodule T K 1 := by
  classical
  apply le_antisymm
  · rintro f ⟨a, rfl⟩
    exact linearPolynomial_isHomogeneous a
  · rw [homogeneousSubmodule_one_eq_span_X]
    apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    exact ⟨coordinatePoint i, linearPolynomial_coordinatePoint i⟩

/-- Every homogeneous linear form is reconstructed from its coordinate-point values. -/
theorem linearPolynomial_eval_coordinate_of_homogeneous [DecidableEq T]
    (f : MvPolynomial T K) (hf : f.IsHomogeneous 1) :
    linearPolynomial (fun i => eval (coordinatePoint i) f) = f := by
  have hmem : f ∈ (linearPolynomialLinearMap (K := K) (T := T)).range := by
    rw [linearPolynomialLinearMap_range]
    exact hf
  obtain ⟨a, ha⟩ := hmem
  change linearPolynomial a = f at ha
  have hcoeff : (fun i => eval (coordinatePoint i) f) = a := by
    funext i
    rw [← ha]
    exact eval_linearPolynomial_coordinate a i
  rw [hcoeff]
  exact ha

end IdealGeneration.QuadraticFlag
