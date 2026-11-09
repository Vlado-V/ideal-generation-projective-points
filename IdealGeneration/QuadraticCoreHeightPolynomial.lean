module

public import IdealGeneration.QuadraticCore
public import IdealGeneration.QuadraticLayerHeightOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The core independence condition is a polynomial in the four selected heights. -/

noncomputable section
namespace IdealGeneration.QuadraticCoreHeight
open MvPolynomial QuadraticLayerHeightOpen

/-- The six actual core points with variable layer heights. -/
def pointMatrix {R : Type*} [Ring R] (a : HeightIndex → R) : Matrix (Fin 6) (Fin 6) R :=
  !![1,-1,1,0,0,0;
     2,-1,0,1,0,0;
     a (false,false),a (false,false),0,0,1,0;
     a (false,true),2*a (false,true),1,1,1,0;
     a (true,false),3*a (true,false),0,0,0,1;
     a (true,true),4*a (true,true),1,1,0,1]

/-- The point matrix commutes with change of coefficient ring. -/
theorem pointMatrix_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (a : HeightIndex → R) :
    (pointMatrix a).map f = pointMatrix (fun h => f (a h)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pointMatrix, map_ofNat]

variable (K : Type*) [Field K]

/-- Nonvanishing certifies independence of the six core cone representatives. -/
def determinant : MvPolynomial HeightIndex K :=
  (pointMatrix (fun h => X (R := K) h)).det

theorem eval_determinant (a : HeightIndex → K) :
    eval a (determinant K) = (pointMatrix a).det := by
  rw [determinant, RingHom.map_det]
  change ((pointMatrix (fun h => X (R := K) h)).map (eval a)).det = (pointMatrix a).det
  rw [pointMatrix_map]
  simp

/-- The explicit witness uses the four layer heights `1,2,1,3`. -/
def witness : HeightIndex → K :=
  fun h => if h.2 then (if h.1 then 3 else 2) else 1

variable [CharZero K]

theorem pointMatrix_witness :
    pointMatrix (witness K) = quadraticCoreConeMatrix.map (Rat.castHom K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pointMatrix, witness, quadraticCoreConeMatrix]

/-- The core determinant can be imposed together with the untouched-pair determinants. -/
theorem determinant_ne_zero : determinant K ≠ 0 := by
  intro h
  have he := eval_determinant K (witness K)
  rw [h, map_zero, pointMatrix_witness K] at he
  exact quadraticCoreConeMatrix_det_ne_zero_over K he.symm

end IdealGeneration.QuadraticCoreHeight
