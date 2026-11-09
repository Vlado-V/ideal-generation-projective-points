module

public import IdealGeneration.CubicB7RootData
public import IdealGeneration.CubicB11Formula

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Closed supported formulas for the two B.7 pool blocks of C.2. -/

namespace IdealGeneration.CubicSupported.B7Root

open B5 RationalChart CubicRationalFormula

def primitiveNat : PrimitiveIndex 12 → ℕ
  | .vertexSlope i d => slopeNat i i d
  | .vertexHeight i d => heightNat i i d
  | .edgeSlope e d => slopeNat e.val.1 e.val.2 d
  | .edgeHeight e d => heightNat e.val.1 e.val.2 d
  | .edgeLambda e => lambdaNat e.val.1 e.val.2

def primitiveFormula (i : PrimitiveIndex 12) : Formula Unit := (primitiveNat i : ℕ)

def sampleFormula (p : Fin 10 × Option (Fin 10 × ℕ)) (b r : Fin 2) :
    B11ProbeFormula Unit 10 where
  support := sampleSupport p
  point i := (sampleCoordinate p i : ℕ)
  weight j := if j = b then 1 else 0
  component := r

def rowFormula0 (i : Fin 86) : B11ProbeFormula Unit 10 :=
  sampleFormula (point0 (rowIndex (n := 43) i).1) 0 (rowIndex (n := 43) i).2

def rowFormula1 (i : Fin 74) : B11ProbeFormula Unit 10 :=
  sampleFormula (point1 (rowIndex (n := 37) i).1) 1 (rowIndex (n := 37) i).2

def formula0 : Matrix (Fin 86) (Fin 86) (Formula Unit) :=
  b11FormulaMatrix primitiveFormula single rowFormula0 column0

def formula1 : Matrix (Fin 74) (Fin 74) (Formula Unit) :=
  b11FormulaMatrix primitiveFormula single rowFormula1 column1

variable {K : Type*} [Field K]

theorem primitiveFormula_matches
    (hne : ∀ a b : ℕ, (a : ZMod 1009) ≠ (b : ZMod 1009) → (a : K) ≠ (b : K))
    (x : Unit → K) (i : PrimitiveIndex 12) :
    Formula.Matches x (primitiveFormula i) (primitiveValue (parameters K hne) i) := by
  cases i <;> exact Formula.Matches.natCast x _

theorem sampleFormula_matches (x : Unit → K) (p : Fin 10 × Option (Fin 10 × ℕ))
    (b r : Fin 2) : (sampleFormula p b r).Matches x
      ⟨fun i => (sampleCoordinate p i : K), pureDirection b, r⟩ where
  point i _ := Formula.Matches.natCast x _
  supported i hi := by simp [sampleCoordinate_eq_zero p i hi]
  weight j := by
    by_cases h : j = b
    · simpa [sampleFormula, pureDirection, h] using Formula.Matches.ofNat x 1
    · simpa [sampleFormula, pureDirection, h] using Formula.Matches.ofNat x 0
  component := rfl

theorem rowFormula0_matches (x : Unit → K) (i : Fin 86) :
    (rowFormula0 i).Matches x (probe0 K i) :=
  sampleFormula_matches x _ _ _

theorem rowFormula1_matches (x : Unit → K) (i : Fin 74) :
    (rowFormula1 i).Matches x (probe1 K i) :=
  sampleFormula_matches x _ _ _

end IdealGeneration.CubicSupported.B7Root
