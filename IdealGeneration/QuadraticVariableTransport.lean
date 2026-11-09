module

public import IdealGeneration.QuadraticMiddleSpace
public import IdealGeneration.ConeSplitting

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Transport from the nested two-normal polynomial ring to the cone coordinates. -/

noncomputable section
namespace IdealGeneration.QuadraticVariableTransport
open MvPolynomial QuadraticElimination

variable {K T H : Type*} [Field K] {m : ℕ} (e : T ≃ Fin m)

/-- Put the two normal variables first, followed by the ordered trace variables. -/
def variableEquiv : Bool ⊕ T ≃ Fin (2 + m) :=
  (Equiv.sumCongr finTwoEquiv.symm e).trans finSumFinEquiv

def traceIndex (j : T) : Fin (2 + m) := (e j).natAdd 2

def normalIndex (b : Bool) : Fin (2 + m) := (finTwoEquiv.symm b).castAdd m

@[simp] theorem variableEquiv_inl (b : Bool) :
    variableEquiv e (.inl b) = normalIndex (m := m) b := by
  simp [variableEquiv, normalIndex, finSumFinEquiv_apply_left]

@[simp] theorem variableEquiv_inr (j : T) : variableEquiv e (.inr j) = traceIndex e j := by
  simp [variableEquiv, traceIndex, finSumFinEquiv_apply_right]

/-- Flatten the normal and trace polynomial rings. -/
def flatten : MvPolynomial Bool (MvPolynomial T K) ≃ₐ[K] Poly K (2 + m) :=
  (MvPolynomial.sumAlgEquiv K Bool T).symm.trans (renameEquiv K (variableEquiv e))

@[simp] theorem flatten_X (b : Bool) :
    flatten (K := K) e (X b) = X (normalIndex (m := m) b) := by
  simp [flatten]

@[simp] theorem flatten_C (f : MvPolynomial T K) :
    flatten (K := K) e (C f) = rename (traceIndex e) f := by
  have h : (flatten (K := K) e).toAlgHom.comp (normalEmbedding (K := K)) = rename (traceIndex e) := by
    ext j
    simp [flatten]
  exact congrArg (fun q : MvPolynomial T K →ₐ[K] Poly K (2 + m) => q f) h

/-- Read the trace coordinates of an ambient representative. -/
def traceAt (z : Fin (2 + m) → K) : T → K := fun j => z (traceIndex e j)

/-- Insert a normal pair and a trace point in the ambient coordinates. -/
def pointOf (u : Bool → K) (x : T → K) : Fin (2 + m) → K :=
  Fin.addCases (u ∘ finTwoEquiv) (x ∘ e.symm)

omit [Field K] in
@[simp] theorem pointOf_normal (u : Bool → K) (x : T → K) (b : Bool) :
    pointOf e u x (normalIndex (m := m) b) = u b := by
  simp [pointOf, normalIndex]

omit [Field K] in
@[simp] theorem pointOf_trace (u : Bool → K) (x : T → K) (j : T) :
    pointOf e u x (traceIndex e j) = x j := by
  simp [pointOf, traceIndex]

/-- Flattening preserves the actual point evaluation. -/
theorem eval_flatten (u : Bool → K) (x : T → K) (f : MvPolynomial Bool (MvPolynomial T K)) :
    eval (pointOf e u x) (flatten e f) = aevalTower (aeval x) u f := by
  have h : (aeval (pointOf e u x) : Poly K (2 + m) →ₐ[K] K).comp (flatten e).toAlgHom =
      aevalTower (aeval x : MvPolynomial T K →ₐ[K] K) u := by
    apply MvPolynomial.algHom_ext'
    · ext j
      change (aeval (pointOf e u x) : Poly K (2 + m) →ₐ[K] K) (flatten e (C (X j))) =
        (aevalTower (aeval x : MvPolynomial T K →ₐ[K] K) u) (C (X j))
      simp [aevalTower_C]
    · intro b
      simp
  exact congrArg (fun f' : MvPolynomial Bool (MvPolynomial T K) →ₐ[K] K => f' f) h

variable [AddCommGroup H] [Module K H]
variable (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K)

/-- The nested represented quadric is the actual ambient polynomial. -/
theorem flatten_normalPolynomialMap (x : LiftSpace (K := K) (H := H)) :
    flatten e (normalPolynomialMap U V g₁ g₂ x) =
      liftedQuadratic (rename (traceIndex e)) (X (normalIndex (m := m) false))
        (X (normalIndex (m := m) true)) U V g₁ g₂ x := by
  simp [liftedQuadratic, quadraticExpression]

/-- The actual represented polynomial is quadratic in the ambient variables. -/
theorem flattenedQuadric_homogeneous
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1)
    (x : LiftSpace (K := K) (H := H)) :
    (flatten e (normalPolynomialMap U V g₁ g₂ x)).IsHomogeneous 2 := by
  rw [flatten_normalPolynomialMap]
  have hs := isHomogeneous_X K (normalIndex (m := m) false)
  have ht := isHomogeneous_X K (normalIndex (m := m) true)
  have hq : (quadraticExpression (X (normalIndex (m := m) false))
      (X (normalIndex (m := m) true))
      (fun i => algebraMap K (Poly K (2 + m)) (x.1 i))).IsHomogeneous 2 := by
    simp only [quadraticExpression, MvPolynomial.algebraMap_eq, mul_assoc]
    exact (((hs.pow 2).C_mul (x.1 0)).add ((hs.mul ht).C_mul (x.1 1))).add
      ((ht.pow 2).C_mul (x.1 2))
  have hu := lowerPart_homogeneous U g₁ hU hg₁ x
  have hv := lowerPart_homogeneous V g₂ hV hg₂ x
  exact (hq.add (hs.mul hu.rename_isHomogeneous)).add (ht.mul hv.rename_isHomogeneous)

@[simp] theorem flattenedQuadric_restrict (x : LiftSpace (K := K) (H := H)) :
    coneRestrict K 2 m (flatten e (normalPolynomialMap U V g₁ g₂ x)) = 0 := by
  have hs (b : Bool) : coneRestrict K 2 m (X (normalIndex (m := m) b)) = 0 :=
    coneRestrict_X_normal K 2 m (finTwoEquiv.symm b)
  rw [flatten_normalPolynomialMap]
  simp [liftedQuadratic, quadraticExpression, hs]

/-- A normal-linear pair becomes the indicated ambient polynomial. -/
theorem flatten_normalPairMap (f : MvPolynomial T K × MvPolynomial T K) :
    flatten e (normalPairMap f) =
      rename (traceIndex e) f.1 * X (normalIndex (m := m) false) +
      rename (traceIndex e) f.2 * X (normalIndex (m := m) true) := by
  simp

theorem flattenedPair_homogeneous {d : ℕ} (f : MvPolynomial T K × MvPolynomial T K)
    (h₁ : f.1.IsHomogeneous d) (h₂ : f.2.IsHomogeneous d) :
    (flatten e (normalPairMap f)).IsHomogeneous (d + 1) := by
  rw [flatten_normalPairMap]
  exact (h₁.rename_isHomogeneous.mul (isHomogeneous_X K _)).add
    (h₂.rename_isHomogeneous.mul (isHomogeneous_X K _))

@[simp] theorem flattenedPair_restrict (f : MvPolynomial T K × MvPolynomial T K) :
    coneRestrict K 2 m (flatten e (normalPairMap f)) = 0 := by
  rw [flatten_normalPairMap]
  simp [normalIndex]

/-- The two-normal source split is the coordinate source written in groups. -/
def splitCoefficients (x : Fin (2 + m) → LiftSpace (K := K) (H := H)) :
    (LiftSpace (K := K) (H := H) × LiftSpace (K := K) (H := H)) ×
      (T → LiftSpace (K := K) (H := H)) :=
  ((x (normalIndex (m := m) false), x (normalIndex (m := m) true)), fun j => x (traceIndex e j))

variable [Fintype T]

/-- Coordinate multiplication commutes with flattening and the source split. -/
theorem flatten_middleMultiplication (x : Fin (2 + m) → LiftSpace (K := K) (H := H)) :
    flatten e (middleMultiplication U V g₁ g₂ (splitCoefficients e x)) =
      ∑ j, X j * flatten e (normalPolynomialMap U V g₁ g₂ (x j)) := by
  rw [← (variableEquiv e).sum_comp (fun j => X j * flatten e (normalPolynomialMap U V g₁ g₂ (x j))),
    Fintype.sum_sum_type, Fintype.sum_bool]
  simp [splitCoefficients, traceProduct]
  abel

end IdealGeneration.QuadraticVariableTransport
