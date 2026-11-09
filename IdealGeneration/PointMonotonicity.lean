module

public import IdealGeneration.Multiplication

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Adding and deleting points

The two algebraic monotonicity arguments in Lemma 2.1. All maps below use
actual homogeneous polynomials and the normalized affine-chart points.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable {K : Type*} [Field K] {n p q d : ℕ}

/-- Retain the points indexed by `e`. -/
def restrictPoints (a : PointCoordinates K n p) (e : Fin q → Fin p) :
    PointCoordinates K n q := fun ij => a (e ij.1, ij.2)

@[simp] theorem chartPoint_restrictPoints (a : PointCoordinates K n p)
    (e : Fin q → Fin p) (i : Fin q) :
    chartPoint K (restrictPoints a e) i = chartPoint K a (e i) := rfl

/-- An equation vanishing on the larger configuration vanishes on its restriction. -/
def restrictEquation (a : PointCoordinates K n p) (e : Fin q → Fin p) (d : ℕ) :
    pointDegreePiece K a d →ₗ[K] pointDegreePiece K (restrictPoints a e) d where
  toFun f := ⟨f.val, by
    apply (mem_pointDegreePiece (restrictPoints a e) _).mpr
    intro i
    exact (mem_pointDegreePiece a _).mp f.property (e i)⟩
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] theorem restrictEquation_val (a : PointCoordinates K n p)
    (e : Fin q → Fin p) (f : pointDegreePiece K a d) :
    (restrictEquation a e d f).val = f.val := rfl

/-- Restriction of the equations is injective. -/
theorem restrictEquation_injective (a : PointCoordinates K n p)
    (e : Fin q → Fin p) : Function.Injective (restrictEquation a e d) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun z : pointDegreePiece K (restrictPoints a e) d => z.val) h)

/-- Restricting equations commutes with multiplication by coordinate variables. -/
theorem restrictEquation_multiplication (a : PointCoordinates K n p)
    (e : Fin q → Fin p) (f : Fin (n + 1) → pointDegreePiece K a d) :
    restrictEquation a e (d + 1) (pointMultiplication a d f) =
      pointMultiplication (restrictPoints a e) d
        (fun j => restrictEquation a e d (f j)) := rfl

/-- Adding points preserves injectivity of the ideal multiplication map. -/
theorem pointMultiplication_injective_of_restriction
    (a : PointCoordinates K n p) (e : Fin q → Fin p)
    (h : Function.Injective (pointMultiplication (restrictPoints a e) d)) :
    Function.Injective (pointMultiplication a d) := by
  intro f g hfg
  have hs : (fun j => restrictEquation a e d (f j)) =
      (fun j => restrictEquation a e d (g j)) := h (by
    rw [← restrictEquation_multiplication, ← restrictEquation_multiplication, hfg])
  funext j
  exact restrictEquation_injective a e (congrFun hs j)

/-- Deleting points preserves surjectivity when the larger configuration has
surjective scalar evaluation in the initial degree. -/
theorem pointMultiplication_surjective_on_restriction
    (a : PointCoordinates K n p) (e : Fin q → Fin p)
    (heval : Function.Surjective (pointEvaluation K a d))
    (hmul : Function.Surjective (pointMultiplication a d)) :
    Function.Surjective (pointMultiplication (restrictPoints a e) d) := by
  intro g
  obtain ⟨f, hf⟩ := heval (pointEvaluation K a (d + 1) g.val)
  let fsmall : pointDegreePiece K (restrictPoints a e) d := ⟨f, by
    apply (mem_pointDegreePiece (restrictPoints a e) _).mpr
    intro i
    have hi := congrFun hf (e i)
    change eval (chartPoint K a (e i)) f.val = _ at hi
    change eval (chartPoint K a (e i)) f.val = 0
    rw [hi]
    exact (mem_pointDegreePiece (restrictPoints a e) _).mp g.property i⟩
  let xf : Forms K (n + 1) (d + 1) :=
    ⟨X (Fin.last n) * f.val, by
      simpa [Nat.add_comm] using (isHomogeneous_X (R := K) (Fin.last n)).mul f.property⟩
  let hlarge : pointDegreePiece K a (d + 1) := ⟨g.val - xf, by
    apply (mem_pointDegreePiece a _).mpr
    intro i
    change eval (chartPoint K a i) (g.val.val - X (Fin.last n) * f.val) = 0
    simp only [map_sub, map_mul, eval_X, chartPoint_last, one_mul]
    exact sub_eq_zero.mpr (congrFun hf i).symm⟩
  obtain ⟨u, hu⟩ := hmul hlarge
  let v : Fin (n + 1) → pointDegreePiece K (restrictPoints a e) d :=
    fun j => restrictEquation a e d (u j) +
      (Pi.single (Fin.last n) fsmall : Fin (n + 1) → pointDegreePiece K (restrictPoints a e) d) j
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have huval := congrArg (fun z => z.val.val) hu
  change (∑ j, X j * (u j).val.val) = g.val.val - X (Fin.last n) * f.val at huval
  change (∑ j, X j * (v j).val.val) = g.val.val
  simp only [v, Submodule.coe_add, restrictEquation_val,
    mul_add, Finset.sum_add_distrib]
  rw [huval]
  have hsingle : (∑ j : Fin (n + 1),
      X j * ((Pi.single (Fin.last n) fsmall :
        Fin (n + 1) → pointDegreePiece K (restrictPoints a e) d) j).val.val) =
      X (Fin.last n) * f.val := by
    classical
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [fsmall]
    · intro j _ hj
      simp [hj]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [hsingle]
  exact sub_add_cancel _ _

end IdealGeneration
