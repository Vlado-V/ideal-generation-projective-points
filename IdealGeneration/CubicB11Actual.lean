module

public import IdealGeneration.CubicPhiLocalColumns
public import IdealGeneration.CubicPhiStarColumns
public import IdealGeneration.CubicPairExtensionLabels
public import IdealGeneration.CubicB11Assembly
public import IdealGeneration.CubicProbeDeformation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The B.7 columns are the first-order values of the actual supported cubic source. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open MvPolynomial Parameters

variable {K : Type*} [Field K] {m : ℕ}

def normalBasis (q r : Fin 3) : K := if r = q then 1 else 0

def linearRemainder (Q : Parameters K (m + 2))
    (c : Fin (m + 2)) (a : Fin 3 → K) (r : Fin 2) : Poly K (m + 2) :=
  ∑ j, C (Q.mixedLinear c a j r) * X j

def motionRemainder (Q : Parameters K (m + 2))
    (b : Fin 2) (i : Fin m) (q : Fin 3) (r : Fin 2) : Poly K (m + 2) :=
  linearRemainder Q (Fin.natAdd m b) (normalBasis q) r -
    linearRemainder Q (Fin.castAdd 2 i) (normalBasis q) r

def crossNormal (Q : Parameters K (m + 2)) (b : Fin 2) (i : Fin m) : Fin 2 → K :=
  ![Q.edgeSlope (crossEdge i b) 0, -1]

def extraRemainder (Q : Parameters K (m + 2))
    (b : Fin 2) (i : Fin m) (u r : Fin 2) : Poly K (m + 2) :=
  linearRemainder Q (Fin.natAdd m b) (shiftLinear u (crossNormal Q b i)) r

/-- The functions used in the block factorization are actual local lift coefficients. -/
def actualB7Data (Q : Parameters K (m + 2)) : B7Data K m where
  cones := Q
  motion b i q y r := eval (extendTrace y) (motionRemainder Q b i q r)
  extra b i u y r := eval (extendTrace y) (extraRemainder Q b i u r)
  remaining b u q y r := eval (extendTrace y)
    (Q.mixedStarRemainder u (Fin.natAdd m b) (normalBasis q) r)

/-- The new-variable direction of an actual lower column. -/
def b7Direction : B7Column m → Fin 2
  | .localColumn b _ => b
  | .motion b _ _ => b
  | .extra b _ _ => b
  | .remaining b _ _ => b

private def localSingle (Q : Parameters K (m + 2)) (hQ : ∀ e, Q.single e = single e)
    {b : Fin 2} (c : LocalColumn m b) : Q.SingleEdge :=
  ⟨localSlopeEdge c, (hQ _).trans (single_localSlopeEdge c)⟩

private def crossSingle (Q : Parameters K (m + 2)) (hQ : ∀ e, Q.single e = single e)
    (b : Fin 2) (i : {i : Fin m // neighbor b i}) : Q.SingleEdge :=
  ⟨crossEdge i.val b, (hQ _).trans ((single_eq_true _).mpr i.property)⟩

/-- The actual eliminated source vectors, with the triangular star-column changes already made. -/
def b7Parameter (Q : Parameters K (m + 2)) (hQ : ∀ e, Q.single e = single e) :
    B7Column m → Q.EliminatedParameters
  | .localColumn b (.inl e) =>
      Q.singleEdgeParameter (Fin.natAdd m b) (localSingle Q hQ (.inl e : LocalColumn m b))
  | .localColumn b (.inr i) =>
      Q.singleEdgeParameter (Fin.castAdd 2 i.2) (localSingle Q hQ (.inr i : LocalColumn m b))
  | .motion b i q => Q.mixedEdgeParameter (crossEdge i b) (normalBasis q)
  | .extra b i u => Q.edgeStarParameter u (crossSingle Q hQ b i)
      (Fin.castAdd 2 i.val) (Fin.natAdd m b)
  | .remaining b u q => Q.mixedStarParameter u (Fin.natAdd m b) (normalBasis q)

/-- The quadratic left after factoring the chosen new variable from a B.7 column. -/
def b7Remainder (Q : Parameters K (m + 2)) (r : Fin 2) : B7Column m → Poly K (m + 2)
  | .localColumn _ c =>
      C (![Q.edgeSlope (localSlopeEdge c) 0, -1] r) *
        X (Fin.castAdd 2 (localEndpoints c).1) * X (Fin.castAdd 2 (localEndpoints c).2)
  | .motion b i q => X (Fin.castAdd 2 i) * motionRemainder Q b i q r
  | .extra b i u => X (Fin.castAdd 2 i.val) * extraRemainder Q b i.val u r
  | .remaining b u q => Q.mixedStarRemainder u (Fin.natAdd m b) (normalBasis q) r

variable {f : ℕ} (Q : Parameters K (m + 2)) (hQ : ∀ e, Q.single e = single e)
variable (free : Fin f → Fin (m + 2) → K) (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

/-- Exact polynomial factorization of each actual lower-column product. -/
theorem parameterPhi_b7Parameter (c : B7Column m) (r : Fin 2) :
    (Q.parameterPhi free h₂ h₆ (b7Parameter Q hQ c) r).val =
      X (Fin.natAdd m (b7Direction c)) * b7Remainder Q r c := by
  cases c with
  | localColumn b c =>
      rcases c with e | ⟨i, j⟩
      · rw [b7Parameter, Q.parameterPhi_singleEdge]
        simp only [b7Direction, b7Remainder, localSingle, localSlopeEdge, oldSlopeEdge,
          localEndpoints, edgeLinear]
        ring
      · rw [b7Parameter, Q.parameterPhi_singleEdge]
        simp only [b7Direction, b7Remainder, localSingle, localSlopeEdge, newSlopeEdge,
          localEndpoints, edgeLinear]
        ring
  | motion b i q =>
      rw [b7Parameter, Q.parameterPhi_mixedEdge]
      simp only [b7Direction, b7Remainder, crossEdge_val, motionRemainder, linearRemainder]
      ring
  | extra b i u =>
      have hj : joins (crossSingle Q hQ b i).val (Fin.castAdd 2 i.val) (Fin.natAdd m b) := Or.inl rfl
      exact Q.parameterPhi_edgeStar free h₂ h₆ u (crossSingle Q hQ b i)
        (Fin.castAdd 2 i.val) (Fin.natAdd m b) hj r
  | remaining b u q =>
      rw [b7Parameter, Q.parameterPhi_mixedStar]
      rfl

private theorem b7Value_eq_remainder (y : Fin m → K) (w : Fin 2 → K) (r : Fin 2)
    (c : B7Column m) :
    b7Value (actualB7Data Q) y w r c =
      w (b7Direction c) * eval (extendTrace y) (b7Remainder Q r c) := by
  cases c with
  | localColumn b c =>
      simp [b7Value, b7Direction, b7Remainder, localValue, actualB7Data]
      ring
  | motion b i q =>
      simp [b7Value, b7Direction, b7Remainder, actualB7Data, mul_assoc]
  | extra b i u =>
      simp [b7Value, b7Direction, b7Remainder, actualB7Data, mul_assoc]
  | remaining b u q =>
      rfl

/-- The first-order actual entry is exactly the B.5 weighted evaluation. -/
theorem movingEvaluation_b7Parameter_coeff_one (y : Fin m → K) (w : Fin 2 → K)
    (c : B7Column m) (r : Fin 2) :
    (movingEvaluation y w (Q.parameterPhi free h₂ h₆ (b7Parameter Q hQ c) r).val).coeff 1 =
      b7Value (actualB7Data Q) y w r c := by
  rw [parameterPhi_b7Parameter Q hQ free h₂ h₆, movingEvaluation_Xnew_coeff_one, b7Value_eq_remainder]

/-- Lower-column evaluations vanish at the initial old-space probe. -/
theorem movingEvaluation_b7Parameter_coeff_zero (y : Fin m → K) (w : Fin 2 → K)
    (c : B7Column m) (r : Fin 2) :
    (movingEvaluation y w (Q.parameterPhi free h₂ h₆ (b7Parameter Q hQ c) r).val).coeff 0 = 0 := by
  rw [parameterPhi_b7Parameter Q hQ free h₂ h₆, movingEvaluation_Xnew, Polynomial.coeff_X_mul_zero]

end IdealGeneration.CubicSupported.B5
