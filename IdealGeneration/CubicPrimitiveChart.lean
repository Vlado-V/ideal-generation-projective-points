module

public import IdealGeneration.CubicSupportedRationalChart

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The admissible primitive cone parameters form an explicit principal open. -/

noncomputable section
namespace IdealGeneration.CubicSupported.RationalChart

open MvPolynomial

variable {K : Type*} [Field K] {m : ℕ}

/-- The nonzero primitive denominators of the supported cone chart. -/
structure PrimitiveAdmissible (single : Edge m → Bool) (x : PrimitiveIndex m → K) : Prop where
  vertexSlope_ne (i : Fin m) : x (.vertexSlope i 0) ≠ x (.vertexSlope i 1)
  vertexHeight_ne (i : Fin m) (d : Fin 2) : x (.vertexHeight i d) ≠ 0
  edgeSlope_ne (e : Edge m) : single e = false → x (.edgeSlope e 0) ≠ x (.edgeSlope e 1)
  edgeHeight_ne (e : Edge m) (d : Fin 2) : x (.edgeHeight e d) ≠ 0
  edgeLambda_ne (e : Edge m) : x (.edgeLambda e) ≠ 0

/-- Every admissible primitive assignment defines the genuine supported cone family. -/
def parametersOfPrimitive (single : Edge m → Bool) (x : PrimitiveIndex m → K)
    (hx : PrimitiveAdmissible single x) : Parameters K m where
  single := single
  vertexSlope i d := x (.vertexSlope i d)
  vertexHeight i d := x (.vertexHeight i d)
  edgeSlope e d := x (.edgeSlope e d)
  edgeHeight e d := x (.edgeHeight e d)
  edgeLambda e := x (.edgeLambda e)
  vertexSlope_ne := hx.vertexSlope_ne
  vertexHeight_ne := hx.vertexHeight_ne
  edgeSlope_ne := hx.edgeSlope_ne
  edgeHeight_ne := hx.edgeHeight_ne
  edgeLambda_ne := hx.edgeLambda_ne

@[simp] theorem primitiveValue_parametersOfPrimitive (single : Edge m → Bool)
    (x : PrimitiveIndex m → K) (hx : PrimitiveAdmissible single x) :
    primitiveValue (parametersOfPrimitive single x hx) = x := by
  funext i
  cases i <;> rfl

theorem primitiveValue_admissible (P : Parameters K m) :
    PrimitiveAdmissible P.single (primitiveValue P) where
  vertexSlope_ne := P.vertexSlope_ne
  vertexHeight_ne := P.vertexHeight_ne
  edgeSlope_ne := P.edgeSlope_ne
  edgeHeight_ne := P.edgeHeight_ne
  edgeLambda_ne := P.edgeLambda_ne

/-- A polynomial whose nonzero set is exactly the admissible chart. -/
def primitiveGuard (single : Edge m → Bool) : MvPolynomial (PrimitiveIndex m) K :=
  (∏ i : Fin m, (X (.vertexSlope i 0) - X (.vertexSlope i 1))) *
    (∏ i : Fin m, ∏ d : Fin 2, X (.vertexHeight i d)) *
    (∏ e : Edge m, if single e then 1 else X (.edgeSlope e 0) - X (.edgeSlope e 1)) *
    (∏ e : Edge m, ∏ d : Fin 2, X (.edgeHeight e d)) *
    ∏ e : Edge m, X (.edgeLambda e)

private theorem eval_primitiveEdgeGuard_ne_zero (single : Edge m → Bool) (x : PrimitiveIndex m → K)
    (e : Edge m) :
    eval x (if single e then 1 else X (.edgeSlope e 0) - X (.edgeSlope e 1)) ≠ 0 ↔
      (single e = false → x (.edgeSlope e 0) ≠ x (.edgeSlope e 1)) := by
  cases single e <;> simp [sub_ne_zero]

/-- Nonzero primitive guard and admissibility are equivalent. -/
theorem eval_primitiveGuard_ne_zero_iff (single : Edge m → Bool) (x : PrimitiveIndex m → K) :
    eval x (primitiveGuard single) ≠ 0 ↔ PrimitiveAdmissible single x := by
  simp only [primitiveGuard, map_mul, map_prod, map_sub, eval_X, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies, sub_ne_zero,
    eval_primitiveEdgeGuard_ne_zero]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · intro h
    exact ⟨⟨⟨⟨h.vertexSlope_ne, h.vertexHeight_ne⟩, h.edgeSlope_ne⟩, h.edgeHeight_ne⟩,
      h.edgeLambda_ne⟩

theorem primitiveGuard_ne_zero_of_chart (P : Parameters K m) :
    primitiveGuard P.single ≠ (0 : MvPolynomial (PrimitiveIndex m) K) := by
  intro h
  have hn := (eval_primitiveGuard_ne_zero_iff P.single (primitiveValue P)).mpr
    (primitiveValue_admissible P)
  exact hn (h ▸ map_zero (eval (primitiveValue P)))

end IdealGeneration.CubicSupported.RationalChart
