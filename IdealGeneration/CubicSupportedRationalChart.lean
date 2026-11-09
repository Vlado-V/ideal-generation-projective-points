module

public import IdealGeneration.CubicLiftDecomposition
public import IdealGeneration.CubicRationalFormula
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Primitive rational formulas for the supported cubic cone chart. -/

noncomputable section
namespace IdealGeneration.CubicSupported.RationalChart

open Parameters CubicRationalFormula

/-- The primitive parameters at the labeled vertex and edge supports. -/
inductive PrimitiveIndex (m : ℕ)
  | vertexSlope (i : Fin m) (d : Fin 2)
  | vertexHeight (i : Fin m) (d : Fin 2)
  | edgeSlope (e : Edge m) (d : Fin 2)
  | edgeHeight (e : Edge m) (d : Fin 2)
  | edgeLambda (e : Edge m)
  deriving DecidableEq, Fintype

variable {K : Type*} [Field K] {m : ℕ}

/-- The actual primitive parameters of a supported chart. -/
def primitiveValue (P : Parameters K m) : PrimitiveIndex m → K
  | .vertexSlope i d => P.vertexSlope i d
  | .vertexHeight i d => P.vertexHeight i d
  | .edgeSlope e d => P.edgeSlope e d
  | .edgeHeight e d => P.edgeHeight e d
  | .edgeLambda e => P.edgeLambda e

variable {σ : Type*}
local notation "F" => Formula σ

def normalLinearFormula (a : Fin 2 → F) (t : F) : F := a 0 + a 1 * t

def normalQuadraticFormula (a : Fin 3 → F) (t : F) : F := a 0 + a 1 * t + a 2 * t ^ 2

def normalCubicFormula (a : Fin 4 → F) (t : F) : F :=
  a 0 + a 1 * t + a 2 * t ^ 2 + a 3 * t ^ 3

def solveTwoFormula (t₀ t₁ r₀ r₁ : F) : Fin 2 → F :=
  let y := (r₁ - r₀) / (t₁ - t₀)
  ![r₀ - t₀ * y, y]

variable (a : PrimitiveIndex m → Formula σ)

private def diagonalRhsFormula (C : Fin 4 → F) (B : Fin m → Fin 3 → F)
    (i : Fin m) (d : Fin 2) : F :=
  let t := a (.vertexSlope i d)
  let μ := a (.vertexHeight i d)
  let numerator := normalCubicFormula C t + μ * normalQuadraticFormula (B i) t
  (-numerator) / (μ ^ (2 : ℕ))

/-- The two vertex coefficients, expressed in the primitive cone data. -/
def diagonalFormula (C : Fin 4 → F) (B : Fin m → Fin 3 → F) (i : Fin m) : Fin 2 → F :=
  solveTwoFormula (a (.vertexSlope i 0)) (a (.vertexSlope i 1))
    (diagonalRhsFormula a C B i 0) (diagonalRhsFormula a C B i 1)

private def edgeRhsFormula (C : Fin 4 → F) (B : Fin m → Fin 3 → F)
    (D : Fin m → Fin 2 → F) (e : Edge m) (d : Fin 2) : F :=
  let t := a (.edgeSlope e d)
  let μ := a (.edgeHeight e d)
  let lam := a (.edgeLambda e)
  let numerator := normalCubicFormula C t + μ * (normalQuadraticFormula (B e.val.1) t +
      lam * normalQuadraticFormula (B e.val.2) t) +
    μ ^ (2 : ℕ) * (normalLinearFormula (D e.val.1) t +
      lam ^ (2 : ℕ) * normalLinearFormula (D e.val.2) t)
  (-numerator) / (μ ^ (2 : ℕ) * lam)

/-- The edge coefficients in the zero free-coordinate gauge. -/
def offDiagonalFormula (single : Edge m → Bool) (C : Fin 4 → F)
    (B : Fin m → Fin 3 → F) (D : Fin m → Fin 2 → F) (e : Edge m) : Fin 2 → F :=
  if single e then ![edgeRhsFormula a C B D e 0, 0]
  else solveTwoFormula (a (.edgeSlope e 0)) (a (.edgeSlope e 1))
    (edgeRhsFormula a C B D e 0) (edgeRhsFormula a C B D e 1)

private def mixedArrayFormula (c : Fin m) (q : Fin 3 → F) (j : Fin m) : Fin 3 → F :=
  if j = c then q else fun _ => 0

private def mixedDiagonalFormula (c : Fin m) (q : Fin 3 → F) (i : Fin m) : Fin 2 → F :=
  if i = c then diagonalFormula a (fun _ => 0) (mixedArrayFormula c q) c
  else fun _ => 0

/-- A mixed coefficient uses only the center's vertex data and one incident edge. -/
def mixedLinearFormula (single : Edge m → Bool) (c : Fin m)
    (q : Fin 3 → F) (j : Fin m) : Fin 2 → F :=
  let C : Fin 4 → F := fun _ => 0
  let B := mixedArrayFormula c q
  let D := mixedDiagonalFormula a c q
  if h : c < j then offDiagonalFormula a single C B D ⟨(c, j), h⟩
  else if h : j < c then offDiagonalFormula a single C B D ⟨(j, c), h⟩
  else diagonalFormula a C B c

/-- The diagonal coefficients of the pure cubic lift. -/
def pureDiagonalFormula (C : Fin 4 → F) (i : Fin m) : Fin 2 → F :=
  diagonalFormula a C (fun _ _ => 0) i

/-- The off-diagonal coefficients of the pure cubic lift. -/
def pureOffDiagonalFormula (single : Edge m → Bool) (C : Fin 4 → F) (e : Edge m) : Fin 2 → F :=
  offDiagonalFormula a single C (fun _ _ => 0) (pureDiagonalFormula a C) e

/-- The ordered coefficient convention used in the normal-linear trace quadratic. -/
def upperCoefficientFormula (diagonal : Fin m → Fin 2 → F)
    (offDiagonal : Edge m → Fin 2 → F) (i j : Fin m) (k : Fin 2) : F :=
  if h : i < j then offDiagonal ⟨(i, j), h⟩ k
  else if i = j then diagonal i k else 0


section Evaluation

variable (x : σ → K)

private theorem matches_zero : Formula.Matches x (0 : F) (0 : K) := by
  simpa using Formula.Matches.ofNat x 0

private theorem normalLinearFormula_matches {a : Fin 2 → F} {t : F}
    {A : Fin 2 → K} {T : K}
    (ha : ∀ k, Formula.Matches x (a k) (A k)) (ht : Formula.Matches x t T) :
    Formula.Matches x (normalLinearFormula a t) (normalLinear A 1 T) := by
  simpa only [normalLinearFormula, normalLinear, mul_one] using (ha 0).add ((ha 1).mul ht)

private theorem normalQuadraticFormula_matches {a : Fin 3 → F} {t : F}
    {A : Fin 3 → K} {T : K}
    (ha : ∀ k, Formula.Matches x (a k) (A k)) (ht : Formula.Matches x t T) :
    Formula.Matches x (normalQuadraticFormula a t) (normalQuadratic A 1 T) := by
  simpa only [normalQuadraticFormula, normalQuadratic, one_pow, mul_one] using
    ((ha 0).add ((ha 1).mul ht)).add ((ha 2).mul (ht.natPow 2))

private theorem normalCubicFormula_matches {a : Fin 4 → F} {t : F}
    {A : Fin 4 → K} {T : K}
    (ha : ∀ k, Formula.Matches x (a k) (A k)) (ht : Formula.Matches x t T) :
    Formula.Matches x (normalCubicFormula a t) (normalCubic A 1 T) := by
  simpa only [normalCubicFormula, normalCubic, one_pow, mul_one] using
    (((ha 0).add ((ha 1).mul ht)).add ((ha 2).mul (ht.natPow 2))).add
      ((ha 3).mul (ht.natPow 3))

private theorem solveTwoFormula_matches {t₀ t₁ r₀ r₁ : F} {T₀ T₁ R₀ R₁ : K}
    (ht₀ : Formula.Matches x t₀ T₀) (ht₁ : Formula.Matches x t₁ T₁)
    (hr₀ : Formula.Matches x r₀ R₀) (hr₁ : Formula.Matches x r₁ R₁)
    (hne : T₀ ≠ T₁) (k : Fin 2) :
    Formula.Matches x (solveTwoFormula t₀ t₁ r₀ r₁ k) (solveTwo T₀ T₁ R₀ R₁ k) := by
  have hy := (hr₁.sub hr₀).div (ht₁.sub ht₀) (sub_ne_zero.mpr (Ne.symm hne))
  fin_cases k
  · exact hr₀.sub (ht₀.mul hy)
  · exact hy

variable (P : Parameters K m) (ha : ∀ i, Formula.Matches x (a i) (primitiveValue P i))
variable {c : Fin 4 → Formula σ} {b : Fin m → Fin 3 → Formula σ} {C : Fin 4 → K} {B : Fin m → Fin 3 → K}

include ha in
private theorem diagonalRhsFormula_matches (hc : ∀ i, Formula.Matches x (c i) (C i))
    (hb : ∀ i j, Formula.Matches x (b i j) (B i j)) (i : Fin m) (d : Fin 2) :
    Formula.Matches x (diagonalRhsFormula a c b i d) (P.diagonalRhs C B i d) := by
  let ht := ha (.vertexSlope i d)
  let hμ := ha (.vertexHeight i d)
  exact ((normalCubicFormula_matches x hc ht).add
    (hμ.mul (normalQuadraticFormula_matches x (hb i) ht))).neg.div (hμ.natPow 2)
      (pow_ne_zero _ (P.vertexHeight_ne i d))

include ha in
/-- The vertex formula is defined and evaluates to the actual chart solve. -/
theorem diagonalFormula_matches (hc : ∀ i, Formula.Matches x (c i) (C i))
    (hb : ∀ i j, Formula.Matches x (b i j) (B i j)) (i : Fin m) (k : Fin 2) :
    Formula.Matches x (diagonalFormula a c b i k) (P.diagonalLift C B i k) :=
  solveTwoFormula_matches x (ha (.vertexSlope i 0)) (ha (.vertexSlope i 1))
    (diagonalRhsFormula_matches a x P ha hc hb i 0)
    (diagonalRhsFormula_matches a x P ha hc hb i 1) (P.vertexSlope_ne i) k

include ha in
private theorem edgeRhsFormula_matches {d : Fin m → Fin 2 → F}
    (hc : ∀ i, Formula.Matches x (c i) (C i))
    (hb : ∀ i j, Formula.Matches x (b i j) (B i j))
    (hd : ∀ i k, Formula.Matches x (d i k) (P.diagonalLift C B i k))
    (e : Edge m) (k : Fin 2) :
    Formula.Matches x (edgeRhsFormula a c b d e k) (P.edgeRhs C B e k) := by
  let ht := ha (.edgeSlope e k)
  let hμ := ha (.edgeHeight e k)
  let hl := ha (.edgeLambda e)
  have hcb := normalCubicFormula_matches x hc ht
  have hb₁ := normalQuadraticFormula_matches x (hb e.val.1) ht
  have hb₂ := normalQuadraticFormula_matches x (hb e.val.2) ht
  have hd₁ := normalLinearFormula_matches x (hd e.val.1) ht
  have hd₂ := normalLinearFormula_matches x (hd e.val.2) ht
  exact ((hcb.add (hμ.mul (hb₁.add (hl.mul hb₂)))).add
    ((hμ.natPow 2).mul (hd₁.add ((hl.natPow 2).mul hd₂)))).neg.div
    ((hμ.natPow 2).mul hl) (mul_ne_zero (pow_ne_zero _ (P.edgeHeight_ne e k)) (P.edgeLambda_ne e))

include ha in
/-- The zero-free-coordinate edge formula is defined and evaluates to the actual chart solve. -/
theorem offDiagonalFormula_matches {d : Fin m → Fin 2 → F}
    (hc : ∀ i, Formula.Matches x (c i) (C i))
    (hb : ∀ i j, Formula.Matches x (b i j) (B i j))
    (hd : ∀ i k, Formula.Matches x (d i k) (P.diagonalLift C B i k))
    (e : Edge m) (k : Fin 2) :
    Formula.Matches x (offDiagonalFormula a P.single c b d e k) (P.offDiagonalLift C B 0 e k) := by
  by_cases hs : P.single e = true
  · fin_cases k
    · simpa [offDiagonalFormula, offDiagonalLift, hs] using edgeRhsFormula_matches a x P ha hc hb hd e 0
    · simpa [offDiagonalFormula, offDiagonalLift, hs] using matches_zero (σ := σ) x
  · have hf := Bool.eq_false_of_not_eq_true hs
    simpa [offDiagonalFormula, offDiagonalLift, hf, primitiveValue] using
      solveTwoFormula_matches x (ha (.edgeSlope e 0)) (ha (.edgeSlope e 1))
        (edgeRhsFormula_matches a x P ha hc hb hd e 0)
        (edgeRhsFormula_matches a x P ha hc hb hd e 1) (P.edgeSlope_ne e hf) k

include ha in
/-- The pure diagonal formula has the value of the actual lifted cubic coefficient. -/
theorem pureDiagonalFormula_matches (hc : ∀ i, Formula.Matches x (c i) (C i))
    (i : Fin m) (k : Fin 2) :
    Formula.Matches x (pureDiagonalFormula a c i k) ((P.pureCubic C).val.2.2.1 i k) := by
  exact diagonalFormula_matches a x P ha (B := 0) hc (fun _ _ => matches_zero x) i k

include ha in
/-- The pure edge formula has the value of the actual lifted cubic coefficient. -/
theorem pureOffDiagonalFormula_matches (hc : ∀ i, Formula.Matches x (c i) (C i))
    (e : Edge m) (k : Fin 2) :
    Formula.Matches x (pureOffDiagonalFormula a P.single c e k) ((P.pureCubic C).val.2.2.2 e k) := by
  exact offDiagonalFormula_matches a x P ha (B := 0) hc (fun _ _ => matches_zero x)
    (fun i j => pureDiagonalFormula_matches a x P ha hc i j) e k


private theorem mixedArrayFormula_matches {q : Fin 3 → F} {Q : Fin 3 → K}
    (hq : ∀ r, Formula.Matches x (q r) (Q r)) (i j : Fin m) (r : Fin 3) :
    Formula.Matches x (mixedArrayFormula i q j r) (mixedArray i Q j r) := by
  by_cases hj : j = i
  · simpa [mixedArrayFormula, mixedArray, hj] using hq r
  · simpa [mixedArrayFormula, mixedArray, hj] using matches_zero (σ := σ) x

include ha in
private theorem mixedDiagonalFormula_matches {q : Fin 3 → F} {Q : Fin 3 → K}
    (hq : ∀ r, Formula.Matches x (q r) (Q r)) (i j : Fin m) (k : Fin 2) :
    Formula.Matches x (mixedDiagonalFormula a i q j k) (P.diagonalLift 0 (mixedArray i Q) j k) := by
  by_cases hj : j = i
  · subst j
    simpa [mixedDiagonalFormula] using diagonalFormula_matches a x P ha (C := 0)
      (fun _ => matches_zero x) (mixedArrayFormula_matches x hq i) i k
  · have hz : P.diagonalLift 0 (mixedArray i Q) j k = 0 := by
      have he := congrFun (congrFun (P.mixedCubic_diagonal i Q) j) k
      change P.diagonalLift 0 (mixedArray i Q) j k = starDiagonal i (P.mixedLinear i Q) j k at he
      simpa [starDiagonal, hj] using he
    simpa [mixedDiagonalFormula, hj, hz] using matches_zero (σ := σ) x

include ha in
/-- The local mixed coefficient is admissible and evaluates to the actual graph lift. -/
theorem mixedLinearFormula_matches {q : Fin 3 → F} {Q : Fin 3 → K}
    (hq : ∀ r, Formula.Matches x (q r) (Q r)) (i j : Fin m) (k : Fin 2) :
    Formula.Matches x (mixedLinearFormula a P.single i q j k) (P.mixedLinear i Q j k) := by
  by_cases hij : i < j
  · simpa [mixedLinearFormula, mixedLinear, mixedCubic, coefficientLift, hij] using
      offDiagonalFormula_matches a x P ha (C := 0) (fun _ => matches_zero x)
        (mixedArrayFormula_matches x hq i) (mixedDiagonalFormula_matches a x P ha hq i)
        ⟨(i, j), hij⟩ k
  · by_cases hji : j < i
    · simpa [mixedLinearFormula, mixedLinear, mixedCubic, coefficientLift, hij, hji] using
        offDiagonalFormula_matches a x P ha (C := 0) (fun _ => matches_zero x)
          (mixedArrayFormula_matches x hq i) (mixedDiagonalFormula_matches a x P ha hq i)
          ⟨(j, i), hji⟩ k
    · simpa [mixedLinearFormula, mixedLinear, mixedCubic, coefficientLift, hij, hji] using
        diagonalFormula_matches a x P ha (C := 0) (fun _ => matches_zero x)
          (mixedArrayFormula_matches x hq i) i k

/-- The upper coefficient selection respects evaluation of its diagonal and edge inputs. -/
theorem upperCoefficientFormula_matches
    {d : Fin m → Fin 2 → F} {e : Edge m → Fin 2 → F}
    {D : Fin m → Fin 2 → K} {E : Edge m → Fin 2 → K}
    (hd : ∀ i k, Formula.Matches x (d i k) (D i k))
    (he : ∀ i k, Formula.Matches x (e i k) (E i k))
    (i j : Fin m) (k : Fin 2) :
    Formula.Matches x (upperCoefficientFormula d e i j k) (upperCoefficient D E i j k) := by
  by_cases hij : i < j
  · simpa [upperCoefficientFormula, upperCoefficient, hij] using he ⟨(i, j), hij⟩ k
  · by_cases heq : i = j
    · simpa [upperCoefficientFormula, upperCoefficient, hij, heq] using hd i k
    · simpa [upperCoefficientFormula, upperCoefficient, hij, heq] using matches_zero (σ := σ) x

end Evaluation
end IdealGeneration.CubicSupported.RationalChart
