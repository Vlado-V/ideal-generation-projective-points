module

public import IdealGeneration.CubicMiddleElimination
public import IdealGeneration.CubicSupportedConfiguration

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The allowed-value target of the supported cubic middle map in (B.2). -/

noncomputable section
namespace IdealGeneration.CubicSupported.Parameters

open CubicMiddle

variable {K : Type*} [Field K] {m f : ℕ} (P : Parameters K m)
  (free : Fin f → Fin m → K)

local notation "C" => P.toConeConfiguration free
local notation "T" => traceLabelEquiv m f
local notation "Values" => Fin (Fintype.card (TraceLabel m f)) → Fin 2 → K

private def valueAt (a : Values) (label : TraceLabel m f) : Fin 2 → K := a (T label)

private theorem normalPairing_vertex (a : Values) (i : Fin m) (d : Fin 2) :
    normalPairing C (P.coneLabelEquiv (.inl (i, d))) a =
      valueAt a (.inl (.inl i)) 0 + P.vertexSlope i d * valueAt a (.inl (.inl i)) 1 := by
  simp [normalPairing, toConeConfiguration, coneNormal, coneSupportLabel, valueAt, Fin.sum_univ_two]

private theorem normalPairing_edge (a : Values) (e : Edge m) (d : Fin 2) (hd : P.EdgeSlot e d) :
    normalPairing C (P.coneLabelEquiv (.inr ⟨(e, d), hd⟩)) a =
      valueAt a (.inl (.inr e)) 0 + P.edgeSlope e d * valueAt a (.inl (.inr e)) 1 := by
  simp [normalPairing, toConeConfiguration, coneNormal, coneSupportLabel, valueAt, Fin.sum_univ_two]

private theorem mem_allowedValues_iff (a : Values) :
    a ∈ allowedValues C ↔
      (∀ i d, valueAt a (.inl (.inl i)) 0 +
        P.vertexSlope i d * valueAt a (.inl (.inl i)) 1 = 0) ∧
      (∀ e d, P.EdgeSlot e d → valueAt a (.inl (.inr e)) 0 +
        P.edgeSlope e d * valueAt a (.inl (.inr e)) 1 = 0) := by
  simp only [allowedValues, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h
    constructor
    · intro i d
      simpa only [normalPairing_vertex] using h (P.coneLabelEquiv (.inl (i, d)))
    · intro e d hd
      simpa only [normalPairing_edge] using h (P.coneLabelEquiv (.inr ⟨(e, d), hd⟩))
  · rintro ⟨hv, he⟩ i
    obtain ⟨label, rfl⟩ := P.coneLabelEquiv.surjective i
    rcases label with ⟨i, d⟩ | ⟨⟨e, d⟩, hd⟩
    · rw [normalPairing_vertex]
      exact hv i d
    · rw [normalPairing_edge]
      exact he e d hd

private theorem value_eq_zero_of_two_slopes (v : Fin 2 → K) {t₀ t₁ : K} (ht : t₀ ≠ t₁)
    (h₀ : v 0 + t₀ * v 1 = 0) (h₁ : v 0 + t₁ * v 1 = 0) : v = 0 := by
  have h : (t₀ - t₁) * v 1 = 0 := by linear_combination h₀ - h₁
  have hv₁ : v 1 = 0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ht)
  have hv₀ : v 0 = 0 := by simpa [hv₁] using h₀
  funext k
  fin_cases k
  · exact hv₀
  · exact hv₁

private def assembleAllowed (z : (P.SingleEdge → K) × (Fin f → Fin 2 → K)) :
    TraceLabel m f → Fin 2 → K
  | .inl (.inl _) => 0
  | .inl (.inr e) =>
      if hs : P.single e = true then ![P.edgeSlope e 0 * z.1 ⟨e, hs⟩, -z.1 ⟨e, hs⟩] else 0
  | .inr j => z.2 j

private def assembleValue (z : (P.SingleEdge → K) × (Fin f → Fin 2 → K)) : Values :=
  fun j => assembleAllowed P z ((traceLabelEquiv m f).symm j)

@[simp] private theorem valueAt_assembleValue (z : (P.SingleEdge → K) × (Fin f → Fin 2 → K))
    (a : TraceLabel m f) : valueAt (assembleValue P z) a = assembleAllowed P z a := by
  simp [valueAt, assembleValue]

private theorem assembleValue_mem (z : (P.SingleEdge → K) × (Fin f → Fin 2 → K)) :
    assembleValue P z ∈ allowedValues C := by
  apply (mem_allowedValues_iff P free _).mpr
  constructor
  · intro i d
    simp [assembleAllowed]
  · intro e d hd
    by_cases hs : P.single e = true
    · have hd₀ : d = 0 := hd.resolve_left (by simp [hs])
      subst d
      simp [assembleAllowed, hs]
    · simp [assembleAllowed, hs]

private def readValue (a : Values) : (P.SingleEdge → K) × (Fin f → Fin 2 → K) :=
  (fun e => -valueAt a (.inl (.inr e.val)) 1, fun j => valueAt a (.inr j))

private theorem assemble_read (a : Values) (ha : a ∈ allowedValues C) :
    assembleValue P (readValue P a) = a := by
  obtain ⟨hv, he⟩ := (mem_allowedValues_iff P free a).mp ha
  funext j
  obtain ⟨label, rfl⟩ := (traceLabelEquiv m f).surjective j
  change valueAt (assembleValue P (readValue P a)) label = valueAt a label
  rw [valueAt_assembleValue]
  rcases label with (i | e) | j
  · have hz := value_eq_zero_of_two_slopes _ (P.vertexSlope_ne i) (hv i 0) (hv i 1)
    simpa only [assembleAllowed] using hz.symm
  · by_cases hs : P.single e = true
    · have h₀ := he e 0 (Or.inr rfl)
      funext k
      fin_cases k
      · simp [assembleAllowed, readValue, hs]
        linear_combination -h₀
      · simp [assembleAllowed, readValue, hs]
    · have hf : P.single e = false := Bool.eq_false_of_not_eq_true hs
      have hz := value_eq_zero_of_two_slopes _ (P.edgeSlope_ne e hf)
        (he e 0 (Or.inl hf)) (he e 1 (Or.inl hf))
      simpa [assembleAllowed, hs] using hz.symm
  · rfl

private theorem read_assemble (z : (P.SingleEdge → K) × (Fin f → Fin 2 → K)) :
    readValue P (assembleValue P z) = z := by
  apply Prod.ext
  · funext e
    simp [readValue, assembleAllowed, e.property]
  · funext j
    simp [readValue, assembleAllowed]

/-- Vertices and double edges have zero allowed values. Single edges contribute one
scalar in direction `(τ,-1)`, and free trace supports contribute two coordinates. -/
def allowedValuesEquiv : allowedValues C ≃ₗ[K]
    ((P.SingleEdge → K) × (Fin f → Fin 2 → K)) where
  toFun a := readValue P a.val
  invFun z := ⟨assembleValue P z, assembleValue_mem P free z⟩
  left_inv a := Subtype.ext (assemble_read P free a.val a.property)
  right_inv := read_assemble P
  map_add' a b := by
    apply Prod.ext
    · funext e
      change -(valueAt a.val (.inl (.inr e.val)) 1 + valueAt b.val (.inl (.inr e.val)) 1) = _
      simp [readValue, add_comm]
    · rfl
  map_smul' r a := by
    apply Prod.ext
    · funext e
      change -(r * valueAt a.val (.inl (.inr e.val)) 1) = _
      simp [readValue, mul_neg]
    · rfl

/-- The allowed-value target dimension counts single-edge and free-support contributions. -/
theorem finrank_allowedValues : Module.finrank K (allowedValues C) =
    Fintype.card P.SingleEdge + 2 * f := by
  rw [(P.allowedValuesEquiv free).finrank_eq, Module.finrank_prod, Module.finrank_pi,
    Module.finrank_pi_fintype]
  simp [mul_comm]

/-- The dimension is twice the number of trace supports minus the number of cone equations. -/
theorem finrank_allowedValues_card : Module.finrank K (allowedValues C) =
    2 * Fintype.card (TraceLabel m f) - Fintype.card P.ConeLabel := by
  rw [P.finrank_allowedValues free, card_traceLabel, P.card_coneLabel]
  have hs : Fintype.card P.SingleEdge ≤ Fintype.card (Edge m) :=
    Fintype.card_subtype_le (fun e : Edge m => P.single e = true)
  omega

end IdealGeneration.CubicSupported.Parameters
