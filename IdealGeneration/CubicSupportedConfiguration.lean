module

public import IdealGeneration.ConeSplitting
public import IdealGeneration.CubicSupportedCoordinates

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The supported graph as an actual marked cone configuration. -/

namespace IdealGeneration.CubicSupported

/-- Labels for the vertex, edge, and free trace representatives. -/
abbrev TraceLabel (m f : ℕ) := (Fin m ⊕ Edge m) ⊕ Fin f

/-- Enumerate the trace representatives by a finite coordinate type. -/
noncomputable def traceLabelEquiv (m f : ℕ) :
    TraceLabel m f ≃ Fin (Fintype.card (TraceLabel m f)) :=
  Fintype.equivFin _

/-- There is one trace representative per vertex, edge, and free label. -/
theorem card_traceLabel (m f : ℕ) :
    Fintype.card (TraceLabel m f) = m + Fintype.card (Edge m) + f := by
  simp only [TraceLabel, Fintype.card_sum, Fintype.card_fin]

namespace Parameters

variable {K : Type*} [Field K] {m : ℕ} (P : Parameters K m)

/-- The actual vertex, edge, and free trace representatives. -/
def traceRepresentative {f : ℕ} (free : Fin f → Fin m → K) :
    TraceLabel m f → Fin m → K
  | .inl (.inl i) => vertexSupport i 1
  | .inl (.inr e) => edgeSupport e 1 (P.edgeLambda e)
  | .inr i => free i

/-- The normal coordinates of a labeled cone point. -/
def coneNormal : P.ConeLabel → Fin 2 → K
  | .inl (i, d) => ![1, P.vertexSlope i d]
  | .inr e => ![1, P.edgeSlope e.val.1 e.val.2]

/-- The height of a labeled cone point over its trace representative. -/
def coneHeight : P.ConeLabel → K
  | .inl (i, d) => P.vertexHeight i d
  | .inr e => P.edgeHeight e.val.1 e.val.2

/-- A cone point is attached to its underlying vertex or edge trace label. -/
def coneSupportLabel {f : ℕ} : P.ConeLabel → TraceLabel m f
  | .inl (i, _) => .inl (.inl i)
  | .inr e => .inl (.inr e.val.1)

/-- Enumerate the valid cone-point labels. -/
noncomputable def coneLabelEquiv : P.ConeLabel ≃ Fin (Fintype.card P.ConeLabel) :=
  Fintype.equivFin _

/-- The marked cone configuration underlying the supported cubic construction. -/
noncomputable def toConeConfiguration {f : ℕ} (free : Fin f → Fin m → K) :
    ConeConfiguration K 2 m (Fintype.card P.ConeLabel) (Fintype.card (TraceLabel m f)) where
  trace j := P.traceRepresentative free ((traceLabelEquiv m f).symm j)
  normal i := P.coneNormal (P.coneLabelEquiv.symm i)
  support i := traceLabelEquiv m f (P.coneSupportLabel (P.coneLabelEquiv.symm i))
  height i := P.coneHeight (P.coneLabelEquiv.symm i)

@[simp] theorem toConeConfiguration_trace {f : ℕ} (free : Fin f → Fin m → K)
    (a : TraceLabel m f) :
    (P.toConeConfiguration free).trace (traceLabelEquiv m f a) =
      P.traceRepresentative free a := by
  simp [toConeConfiguration]

@[simp] theorem toConeConfiguration_support {f : ℕ} (free : Fin f → Fin m → K)
    (a : P.ConeLabel) :
    (P.toConeConfiguration free).support (P.coneLabelEquiv a) =
      traceLabelEquiv m f (P.coneSupportLabel a) := by
  simp [toConeConfiguration]

/-- The configuration has exactly the representatives used by the coefficient evaluation map. -/
@[simp] theorem toConeConfiguration_point {f : ℕ} (free : Fin f → Fin m → K)
    (a : P.ConeLabel) :
    (P.toConeConfiguration free).point (P.coneLabelEquiv a) = P.conePoint a := by
  funext k
  unfold ConeConfiguration.point
  cases a with
  | inl v =>
    rcases v with ⟨i, d⟩
    simp [toConeConfiguration, coneNormal, coneHeight,
      coneSupportLabel, traceRepresentative, conePoint, vertexPoint, vertexSupport, mul_ite]
    rfl
  | inr e =>
    simp [toConeConfiguration, coneNormal, coneHeight,
      coneSupportLabel, traceRepresentative, conePoint, edgePoint, edgeSupport, vertexSupport,
      mul_add, mul_ite]
    rfl

/-- The omitted slots are exactly the second slots at single edges. -/
private def omittedEdgeSlotEquiv :
    {p : Edge m × Fin 2 // ¬ P.EdgeSlot p.1 p.2} ≃ P.SingleEdge where
  toFun p := ⟨p.val.1, Bool.eq_true_of_not_eq_false (fun hf => p.property (Or.inl hf))⟩
  invFun e := ⟨(e.val, 1), by
    intro h
    rcases h with hf | hd
    · simp [e.property] at hf
    · exact (by decide : (1 : Fin 2) ≠ 0) hd⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, (1 : Fin 2)) = p.val
    exact Prod.ext rfl (Fin.eq_one_of_ne_zero p.val.2
      (fun hd => p.property (Or.inr hd))).symm
  right_inv e := Subtype.ext rfl

/-- Each vertex has two cone points, and each single edge omits one slot. -/
theorem card_coneLabel :
    Fintype.card P.ConeLabel =
      2 * m + 2 * Fintype.card (Edge m) - Fintype.card P.SingleEdge := by
  have homitted := Fintype.card_congr (P.omittedEdgeSlotEquiv)
  rw [Fintype.card_subtype_compl] at homitted
  have hvalid := Fintype.card_subtype_le (fun p : Edge m × Fin 2 => P.EdgeSlot p.1 p.2)
  simp only [Fintype.card_prod, Fintype.card_fin] at homitted hvalid
  simp only [ConeLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

end Parameters
end IdealGeneration.CubicSupported
