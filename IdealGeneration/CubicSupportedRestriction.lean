module

public import IdealGeneration.CubicSupportedKernel
public import IdealGeneration.QuadraticTraceRestriction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Restriction to the old trace coordinates in a pair addition of Appendix B.4. -/

namespace IdealGeneration.CubicSupported

open MvPolynomial
open QuadraticTraceRestriction (restrictPolynomial restrict_X_embedded restrict_X_off
  extendPoint extendPoint_embedded extendPoint_off eval_restrict)

variable {K : Type*} [Field K] {m : ℕ}

/-- The increasing edges between old vertices inside the enlarged graph. -/
def oldEdge (m : ℕ) : Edge m ↪ Edge (m + 2) where
  toFun e := ⟨(Fin.castAdd 2 e.val.1, Fin.castAdd 2 e.val.2), e.property⟩
  inj' e f h := by
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (congrArg (fun e : Edge (m + 2) => e.val.1.val) h)
    · exact Fin.ext (congrArg (fun e : Edge (m + 2) => e.val.2.val) h)

@[simp] theorem oldEdge_val (e : Edge m) :
    (oldEdge m e).val = (Fin.castAdd 2 e.val.1, Fin.castAdd 2 e.val.2) := rfl

/-- All cone data on an old support agree after adding the two coordinates. -/
structure Compatible (P : Parameters K m) (Q : Parameters K (m + 2)) : Prop where
  single_eq (e : Edge m) : Q.single (oldEdge m e) = P.single e
  vertexSlope_eq (i : Fin m) (d : Fin 2) : Q.vertexSlope (Fin.castAdd 2 i) d = P.vertexSlope i d
  vertexHeight_eq (i : Fin m) (d : Fin 2) : Q.vertexHeight (Fin.castAdd 2 i) d = P.vertexHeight i d
  edgeSlope_eq (e : Edge m) (d : Fin 2) : Q.edgeSlope (oldEdge m e) d = P.edgeSlope e d
  edgeHeight_eq (e : Edge m) (d : Fin 2) : Q.edgeHeight (oldEdge m e) d = P.edgeHeight e d
  edgeLambda_eq (e : Edge m) : Q.edgeLambda (oldEdge m e) = P.edgeLambda e

/-- Extend trace coordinates by zero in the two new slots. -/
def extendTrace {R : Type*} [Zero R] (y : Fin m → R) : Fin (m + 2) → R :=
  Fin.addCases y 0

@[simp] theorem extendTrace_old {R : Type*} [Zero R] (y : Fin m → R) (i : Fin m) :
    extendTrace y (Fin.castAdd 2 i) = y i := Fin.addCases_left i

@[simp] theorem extendTrace_new {R : Type*} [Zero R] (y : Fin m → R) (j : Fin 2) :
    extendTrace y (Fin.natAdd m j) = 0 := Fin.addCases_right j

/-- Retain the normal coordinates and the old trace coordinates. -/
def oldCoordinates (m : ℕ) : Fin (2 + m) ↪ Fin (2 + (m + 2)) :=
  Fin.castLEEmb (by omega)

@[simp] theorem oldCoordinates_normal (k : Fin 2) :
    oldCoordinates m (Fin.castAdd m k) = Fin.castAdd (m + 2) k := Fin.ext rfl

@[simp] theorem oldCoordinates_trace (i : Fin m) :
    oldCoordinates m (Fin.natAdd 2 i) = Fin.natAdd 2 (Fin.castAdd 2 i) := Fin.ext rfl

private theorem newTrace_off_oldCoordinates (j : Fin 2) :
    Fin.natAdd 2 (Fin.natAdd m j) ∉ Set.range (oldCoordinates m) := by
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  change i.val = 2 + (m + j.val) at he
  omega

/-- Restriction of the coefficients of a positive-normal-degree cubic. -/
def restrictCoefficients : Coefficients K (m + 2) →ₗ[K] Coefficients K m where
  toFun u := (u.1, fun i => u.2.1 (Fin.castAdd 2 i),
    fun i => u.2.2.1 (Fin.castAdd 2 i), fun e => u.2.2.2 (oldEdge m e))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Upper coefficients at old endpoints agree with the restricted coefficients. -/
theorem upperCoefficient_old {R : Type*} [CommRing R]
    (a : Fin (m + 2) → Fin 2 → R) (b : Edge (m + 2) → Fin 2 → R)
    (i j : Fin m) (k : Fin 2) :
    upperCoefficient a b (Fin.castAdd 2 i) (Fin.castAdd 2 j) k =
      upperCoefficient (fun i => a (Fin.castAdd 2 i)) (fun e => b (oldEdge m e)) i j k := by
  have hlt : Fin.castAdd 2 i < Fin.castAdd 2 j ↔ i < j := Iff.rfl
  have heq : Fin.castAdd 2 i = Fin.castAdd 2 j ↔ i = j := (Fin.castAddEmb 2).injective.eq_iff
  by_cases hij : i < j
  · calc
      _ = b (oldEdge m ⟨(i, j), hij⟩) k :=
        upperCoefficient_edge a b (oldEdge m ⟨(i, j), hij⟩) k
      _ = _ := (upperCoefficient_edge (fun i => a (Fin.castAdd 2 i))
        (fun e => b (oldEdge m e)) ⟨(i, j), hij⟩ k).symm
  · by_cases h : i = j
    · subst j
      simp
    · simp [upperCoefficient, hij, hlt.not.mpr hij, h, heq.not.mpr h]

private theorem cubicValue_extendTrace {R : Type*} [CommRing R]
    (C : Fin 4 → R) (B : Fin (m + 2) → Fin 3 → R)
    (a : Fin (m + 2) → Fin 2 → R) (b : Edge (m + 2) → Fin 2 → R)
    (s t : R) (y : Fin m → R) :
    cubicValue C B a b s t (extendTrace y) =
      cubicValue C (fun i => B (Fin.castAdd 2 i)) (fun i => a (Fin.castAdd 2 i))
        (fun e => b (oldEdge m e)) s t y := by
  simp only [cubicValue, traceQuadratic, Fin.sum_univ_add, extendTrace_old, extendTrace_new,
    upperCoefficient_old, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

/-- Polynomial specialization retains exactly the old coefficients. -/
theorem restrictCoefficientPolynomial (u : Coefficients K (m + 2)) :
    restrictPolynomial K (oldCoordinates m) (coefficientPolynomial u) =
      coefficientPolynomial (restrictCoefficients u) := by
  let f := restrictPolynomial K (oldCoordinates m)
  have hn (k : Fin 2) : f (X (Fin.castAdd (m + 2) k)) = X (Fin.castAdd m k) := by
    rw [← oldCoordinates_normal (m := m) k]
    exact restrict_X_embedded K (oldCoordinates m) _
  have ht : (fun i : Fin (m + 2) => f (X (Fin.natAdd 2 i))) =
      extendTrace (fun i : Fin m => X (Fin.natAdd 2 i)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [extendTrace_old, ← oldCoordinates_trace]
      exact restrict_X_embedded K (oldCoordinates m) _
    · rw [extendTrace_new]
      exact restrict_X_off K (oldCoordinates m) (newTrace_off_oldCoordinates j)
  change f (polynomial u.1 u.2.1 u.2.2.1 u.2.2.2) = _
  simp only [coefficientPolynomial_apply, polynomial]
  rw [show (f : Poly K (2 + (m + 2)) → Poly K (2 + m)) = f.toRingHom from rfl,
    map_cubicValue]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.algHom_C, hn, ht]
  exact cubicValue_extendTrace _ _ _ _ _ _ _

/-- Extending an old point leaves its normal coordinates in place and extends its trace by zero. -/
theorem extendPoint_addCases (a : Fin 2 → K) (y : Fin m → K) :
    extendPoint K (oldCoordinates m) (Fin.addCases a y) =
      Fin.addCases a (extendTrace y) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun i => ?_) j
  · rw [← oldCoordinates_normal (m := m) k, extendPoint_embedded]
    simp
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [← oldCoordinates_trace (m := m) i, extendPoint_embedded]
      simp [Fin.addCases_right]
    · rw [extendPoint_off K (oldCoordinates m) _ (newTrace_off_oldCoordinates i)]
      simp [Fin.addCases_right]

private theorem extendTrace_vertexSupport (i : Fin m) (μ : K) :
    extendTrace (vertexSupport i μ) = vertexSupport (Fin.castAdd 2 i) μ := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [extendTrace_old]
    simp [vertexSupport]
  · have hne : Fin.natAdd m j ≠ Fin.castAdd 2 i := by
      intro h
      have he := congrArg Fin.val h
      change m + j.val = i.val at he
      omega
    simp [vertexSupport, hne]

private theorem extendTrace_edgeSupport (e : Edge m) (μ lam : K) :
    extendTrace (edgeSupport e μ lam) = edgeSupport (oldEdge m e) μ lam := by
  have hadd (x y : Fin m → K) : extendTrace (x + y) = extendTrace x + extendTrace y := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  change extendTrace (vertexSupport e.val.1 μ + vertexSupport e.val.2 (μ * lam)) =
    vertexSupport (Fin.castAdd 2 e.val.1) μ +
      vertexSupport (Fin.castAdd 2 e.val.2) (μ * lam)
  rw [hadd, extendTrace_vertexSupport, extendTrace_vertexSupport]

namespace Compatible

variable {P : Parameters K m} {Q : Parameters K (m + 2)} (h : Compatible P Q)

/-- Old single-edge coordinates embed in the single-edge coordinates after the addition. -/
def singleEdge : P.SingleEdge ↪ Q.SingleEdge where
  toFun e := ⟨oldEdge m e.val, (h.single_eq e.val).trans e.property⟩
  inj' _ _ he := Subtype.ext ((oldEdge m).injective (congrArg Subtype.val he))

@[simp] theorem singleEdge_val (e : P.SingleEdge) :
    (h.singleEdge e).val = oldEdge m e.val := rfl

/-- Compatibility retains every old cone slot. -/
def coneLabel : P.ConeLabel → Q.ConeLabel
  | .inl (i, d) => .inl (Fin.castAdd 2 i, d)
  | .inr ⟨(e, d), hd⟩ => .inr ⟨(oldEdge m e, d), by
      simpa only [Parameters.EdgeSlot, h.single_eq e] using hd⟩

theorem extendPoint_conePoint (a : P.ConeLabel) :
    extendPoint K (oldCoordinates m) (P.conePoint a) = Q.conePoint (h.coneLabel a) := by
  rcases a with ⟨i, d⟩ | ⟨⟨e, d⟩, hd⟩
  · change extendPoint K (oldCoordinates m)
      (Fin.addCases ![1, P.vertexSlope i d] (vertexSupport i (P.vertexHeight i d))) =
      Fin.addCases ![1, Q.vertexSlope (Fin.castAdd 2 i) d]
        (vertexSupport (Fin.castAdd 2 i) (Q.vertexHeight (Fin.castAdd 2 i) d))
    rw [extendPoint_addCases, extendTrace_vertexSupport, h.vertexSlope_eq, h.vertexHeight_eq]
  · change extendPoint K (oldCoordinates m)
      (Fin.addCases ![1, P.edgeSlope e d] (edgeSupport e (P.edgeHeight e d) (P.edgeLambda e))) =
      Fin.addCases ![1, Q.edgeSlope (oldEdge m e) d]
        (edgeSupport (oldEdge m e) (Q.edgeHeight (oldEdge m e) d) (Q.edgeLambda (oldEdge m e)))
    rw [extendPoint_addCases, extendTrace_edgeSupport, h.edgeSlope_eq, h.edgeHeight_eq,
      h.edgeLambda_eq]

/-- Restriction of supported kernel cubics to the old coordinates. -/
noncomputable def restrictKernel : Q.coefficientKernel →ₗ[K] P.coefficientKernel where
  toFun u := ⟨restrictCoefficients u.val, (P.mem_coefficientKernel _).mpr fun a => by
    rw [← restrictCoefficientPolynomial, eval_restrict, h.extendPoint_conePoint]
    exact (Q.mem_coefficientKernel u.val).mp u.property (h.coneLabel a)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem restrictKernel_val (u : Q.coefficientKernel) :
    (h.restrictKernel u).val = restrictCoefficients u.val := rfl

/-- The pure normal cubic component is unchanged by restriction. -/
@[simp] theorem restrictKernel_pureNormal (u : Q.coefficientKernel) :
    (h.restrictKernel u).val.1 = u.val.1 := rfl

@[simp] theorem restrictKernel_mixed (u : Q.coefficientKernel) (i : Fin m) :
    (h.restrictKernel u).val.2.1 i = u.val.2.1 (Fin.castAdd 2 i) := rfl

@[simp] theorem restrictKernel_diagonal (u : Q.coefficientKernel) (i : Fin m) :
    (h.restrictKernel u).val.2.2.1 i = u.val.2.2.1 (Fin.castAdd 2 i) := rfl

@[simp] theorem restrictKernel_offDiagonal (u : Q.coefficientKernel) (e : Edge m) :
    (h.restrictKernel u).val.2.2.2 e = u.val.2.2.2 (oldEdge m e) := rfl

/-- Specialization of the actual polynomial of a kernel cubic. -/
theorem restrictKernel_polynomial (u : Q.coefficientKernel) :
    restrictPolynomial K (oldCoordinates m) (coefficientPolynomial u.val) =
      coefficientPolynomial (h.restrictKernel u).val :=
  restrictCoefficientPolynomial u.val

/-- The mixed quadratic component is restricted to the old trace indices. -/
theorem topProjection_restrictKernel (u : Q.coefficientKernel) :
    P.topProjection (h.restrictKernel u) =
      ((Q.topProjection u).1, fun i => (Q.topProjection u).2 (Fin.castAdd 2 i)) := rfl

@[simp] theorem freeCoefficients_restrictKernel (u : Q.coefficientKernel) (e : P.SingleEdge) :
    P.freeCoefficients (h.restrictKernel u) e = Q.freeCoefficients u (h.singleEdge e) := rfl

/-- B.4 restriction is surjective by extending the mixed and free coordinates by zero. -/
theorem restrictKernel_surjective : Function.Surjective h.restrictKernel := by
  intro u
  let z : Q.SingleEdge → K := Function.extend h.singleEdge (P.freeCoefficients u) 0
  let c := (u.val.1, extendTrace u.val.2.1, z)
  let v := Q.kernelCoordinatesEquiv.symm c
  have hv := Q.kernelCoordinatesEquiv.apply_symm_apply c
  change (v.val.1, v.val.2.1, Q.freeCoefficients v) = c at hv
  have hC : v.val.1 = u.val.1 := congrArg Prod.fst hv
  have hB : v.val.2.1 = extendTrace u.val.2.1 := congrArg (fun p => p.2.1) hv
  have hz : Q.freeCoefficients v = z := congrArg (fun p => p.2.2) hv
  refine ⟨v, P.kernelCoordinatesEquiv.injective ?_⟩
  change ((h.restrictKernel v).val.1, (h.restrictKernel v).val.2.1,
    P.freeCoefficients (h.restrictKernel v)) = (u.val.1, u.val.2.1, P.freeCoefficients u)
  refine Prod.ext hC (Prod.ext ?_ ?_)
  · funext i
    change v.val.2.1 (Fin.castAdd 2 i) = u.val.2.1 i
    rw [hB, extendTrace_old]
  · funext e
    change P.freeCoefficients (h.restrictKernel v) e = P.freeCoefficients u e
    rw [freeCoefficients_restrictKernel, hz]
    exact h.singleEdge.injective.extend_apply _ _ e

end Compatible
end IdealGeneration.CubicSupported
