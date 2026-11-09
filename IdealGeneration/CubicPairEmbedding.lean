module

public import IdealGeneration.CubicPairRationalConstruction
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Coordinate embeddings of the cubic pair block

The local coordinates `3,4` are the two old pair coordinates. Coordinates `5,6`
are the direction weights. A row supported away from the pair sets coordinates
`3,4` to zero and annihilates every local pair column.
-/

namespace IdealGeneration.CubicPair

section Support

variable {R : Type*} [CommRing R]

/-- All pair columns vanish when both old pair coordinates vanish. -/
theorem functionColumn_eq_zero_of_pairCoordinates_zero
    (coeff : PairLiftCoefficients R) (t1 t2 : R) (c : Fin 26)
    (x : Fin 7 → R) (k : Fin 2) (h3 : x 3 = 0) (h4 : x 4 = 0) :
    functionColumn coeff t1 t2 c x k = 0 := by
  fin_cases c <;> simp [functionColumn, halfFaceValue, h3, h4]

end Support

section Rename

open MvPolynomial
variable {K ι : Type*} [Field K]

/-- Rename the coordinates of a two-component polynomial. -/
noncomputable def renamePairVector (e : Fin 7 → ι) :
    (Fin 2 → MvPolynomial (Fin 7) K) →ₗ[K] (Fin 2 → MvPolynomial ι K) where
  toFun p k := rename e (p k)
  map_add' p q := by ext k; simp
  map_smul' a p := by ext k; simp

/-- An injective coordinate map gives an injective map on vector-valued polynomials. -/
theorem renamePairVector_injective (e : Fin 7 → ι) (he : Function.Injective e) :
    Function.Injective (renamePairVector (K := K) e) := by
  intro p q hpq
  funext k
  exact rename_injective e he (congrFun hpq k)

/-- Coordinate renaming commutes with evaluation of each pair column. -/
theorem eval_rename_polynomialColumn
    (e : Fin 7 → ι) (coeff : PairLiftCoefficients K) (t1 t2 : K)
    (c : Fin 26) (x : ι → K) (k : Fin 2) :
    eval x (rename e (polynomialColumn coeff t1 t2 c k)) =
      functionColumn coeff t1 t2 c (x ∘ e) k := by
  rw [eval_rename, eval_polynomialColumn]

/-- Every renamed pair column vanishes on a row supported away from its pair. -/
theorem eval_rename_polynomialColumn_eq_zero
    (e : Fin 7 → ι) (coeff : PairLiftCoefficients K) (t1 t2 : K)
    (c : Fin 26) (x : ι → K) (k : Fin 2)
    (h3 : x (e 3) = 0) (h4 : x (e 4) = 0) :
    eval x (rename e (polynomialColumn coeff t1 t2 c k)) = 0 := by
  rw [eval_rename_polynomialColumn]
  exact functionColumn_eq_zero_of_pairCoordinates_zero coeff t1 t2 c (x ∘ e) k h3 h4

/-- Renaming injectively preserves independence of an entire pair-column family. -/
theorem polynomialColumn_linearIndependent_rename
    (e : Fin 7 → ι) (he : Function.Injective e)
    (coeff : PairLiftCoefficients K) (t1 t2 : K)
    (h : LinearIndependent K (polynomialColumn coeff t1 t2)) :
    LinearIndependent K (fun c k => rename e (polynomialColumn coeff t1 t2 c k)) := by
  exact h.map' (renamePairVector e) (LinearMap.ker_eq_bot.mpr (renamePairVector_injective e he))

/-- Coordinate renaming preserves the homogeneous cubic degree of each weighted column. -/
theorem rename_polynomialColumn_isHomogeneous
    (e : Fin 7 → ι) (coeff : PairLiftCoefficients K) (t1 t2 : K)
    (c : Fin 26) (k : Fin 2) :
    (rename e (polynomialColumn coeff t1 t2 c k)).IsHomogeneous 3 :=
  (polynomialColumn_isHomogeneous coeff t1 t2 c k).rename_isHomogeneous

end Rename

section PrimitiveConstruction

open MvPolynomial
variable (K : Type*) [Field K] [CharZero K]
variable {ι : Type*}

/-- The primitive-parameter characteristic-zero pair columns in ambient coordinates. -/
noncomputable def primitiveEmbeddedPairColumns (e : Fin 7 → ι)
    (c : Fin 26) (k : Fin 2) : MvPolynomial ι K :=
  rename e (polynomialColumn
    (fun a q j l => (RationalConstruction.primitiveLiftCoefficientsQ a q j l : K))
    (810 : K) (479 : K) c k)

/-- The actual primitive pair columns stay independent in every injective coordinate embedding. -/
theorem primitiveEmbeddedPairColumns_linearIndependent
    (e : Fin 7 → ι) (he : Function.Injective e) :
    LinearIndependent K (primitiveEmbeddedPairColumns K e) :=
  polynomialColumn_linearIndependent_rename e he _ _ _
    (RationalConstruction.primitivePairColumns_linearIndependent_over K)

omit [CharZero K] in
/-- Pool rows and rows of another pair annihilate the embedded columns whenever
neither coordinate of this pair belongs to their support. -/
theorem primitiveEmbeddedPairColumns_vanish
    (e : Fin 7 → ι) (c : Fin 26) (x : ι → K) (k : Fin 2)
    (h3 : x (e 3) = 0) (h4 : x (e 4) = 0) :
    eval x (primitiveEmbeddedPairColumns K e c k) = 0 := by
  exact eval_rename_polynomialColumn_eq_zero e _ _ _ c x k h3 h4

omit [CharZero K] in
/-- Each embedded primitive column is still homogeneous of degree three. -/
theorem primitiveEmbeddedPairColumns_isHomogeneous
    (e : Fin 7 → ι) (c : Fin 26) (k : Fin 2) :
    (primitiveEmbeddedPairColumns K e c k).IsHomogeneous 3 :=
  rename_polynomialColumn_isHomogeneous e _ _ _ c k

end PrimitiveConstruction
end IdealGeneration.CubicPair
