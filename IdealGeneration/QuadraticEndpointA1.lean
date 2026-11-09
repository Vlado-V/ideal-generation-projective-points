module

public import IdealGeneration.ConeA1Bridge
public import IdealGeneration.CriticalOpen
public import IdealGeneration.QuadraticTracePostulation
public import IdealGeneration.QuadraticCanonicalConeConfiguration
public import IdealGeneration.QuadraticMiddleEndpoint
public import IdealGeneration.QuadraticTruncatedEndpoint

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The numerical endpoints of the quadratic marked-cone step

The two trace dimensions have integral quadratic critical counts. The
flag and its selected probes realize these trace counts, and the cone
counts place the ambient examples at the required critical endpoints.
-/

noncomputable section
namespace IdealGeneration.QuadraticEndpointA1
open Module MvPolynomial QuadraticFlag QuadraticTracePostulation
open ConeParameterSpace ConeMiddleFamily

private theorem flag_even_count (k l : ℕ) :
    flagCount (2 * k) l = k * (2 * k + 1) + l * (k + 1) := by
  have hN := two_mul_quadratic_count (2 * k)
  have hn : N (2 * k) 2 = k * (2 * k + 1) := by nlinarith
  have hhalf : (2 * k) / 2 = k := by omega
  rw [flagCount, hn, hhalf]

/-- The first surjective endpoint uses every available extra probe. -/
theorem flag_count_mod_two (ν : ℕ) (hν : 2 ≤ ν) :
    flagCount (2 * (ν - 1)) (ν + 2) + (2 * (ν - 1) + 1) = ν * (3 * ν + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ ν by omega)
  rw [show k + 1 - 1 = k by omega, flag_even_count]
  ring

/-- The two endpoints in the other congruence class use one extra point per pair. -/
theorem flag_count_mod_one (ν : ℕ) (hν : 2 ≤ ν) :
    flagCount (2 * (ν - 1)) (ν + 1) + (ν - 1) = ν * (3 * ν - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ ν by omega)
  rw [show k + 1 - 1 = k by omega, flag_even_count,
    show 3 * (k + 1) - 1 = 3 * k + 2 by omega]
  ring

private theorem trace_balance {m q : ℕ} (hm : 1 ≤ m) (hq : 3 * q = 2 * N m 2) :
    m * (N m 2 - q) = N m 3 - q := by
  have hr : 3 * (N m 2 - q) = N m 2 := by omega
  have he : 3 * (m * (N m 2 - q) + q) = 3 * N m 3 := by
    calc
      _ = m * (3 * (N m 2 - q)) + 3 * q := by ring
      _ = (m + 2) * N m 2 := by rw [hr, hq]; ring
      _ = _ := (N_degree_recurrence m 2 hm).symm
  omega

/-- The trace block is square in `3ν` homogeneous variables. -/
theorem trace_balance_mod_two (ν : ℕ) (hν : 2 ≤ ν) :
    (3 * ν) * (N (3 * ν) 2 - ν * (3 * ν + 1)) = N (3 * ν) 3 - ν * (3 * ν + 1) := by
  apply trace_balance (by omega)
  rw [two_mul_quadratic_count]
  ring

/-- The trace block is square in `3ν−1` homogeneous variables. -/
theorem trace_balance_mod_one (ν : ℕ) (hν : 2 ≤ ν) :
    (3 * ν - 1) * (N (3 * ν - 1) 2 - ν * (3 * ν - 1)) =
      N (3 * ν - 1) 3 - ν * (3 * ν - 1) := by
  apply trace_balance (by omega)
  rw [two_mul_quadratic_count, show 3 * ν - 1 + 1 = 3 * ν by omega]
  ring

private theorem critical_counts_integral {n t : ℕ} (ht : 3 * t = 2 * N n 2) :
    N n 2 - lowerCritical n 2 = t ∧ N n 2 - upperCritical n 2 = t := by
  have ht' : t ≤ N n 2 := by omega
  have hr : 3 * (N n 2 - t) = N n 2 := by omega
  have hq : (3 : ℚ) * ((N n 2 - t : ℕ) : ℚ) = (N n 2 : ℚ) := by exact_mod_cast hr
  have he : E n 2 = ((N n 2 - t : ℕ) : ℚ) := by
    unfold E
    norm_num
    linarith
  have hl : lowerCritical n 2 = N n 2 - t := by simp [lowerCritical, he]
  have hu : upperCritical n 2 = N n 2 - t := by simp [upperCritical, he]
  exact ⟨by rw [hl, Nat.sub_sub_self ht'], by rw [hu, Nat.sub_sub_self ht']⟩

private theorem critical_counts_residue_one {n t : ℕ} (ht : 3 * t + 2 = 2 * N n 2) :
    N n 2 - lowerCritical n 2 = t + 1 ∧ N n 2 - upperCritical n 2 = t := by
  have hti : t + 1 ≤ N n 2 := by omega
  let rI := N n 2 - (t + 1)
  let rS := N n 2 - t
  have hrI : 3 * rI + 1 = N n 2 := by dsimp [rI]; omega
  have hrS : 3 * rS = N n 2 + 2 := by dsimp [rS]; omega
  have hrSpos : 1 ≤ rS := by omega
  have hiq : (3 : ℚ) * (rI : ℚ) + 1 = (N n 2 : ℚ) := by exact_mod_cast hrI
  have hsq : (3 : ℚ) * (rS : ℚ) = (N n 2 : ℚ) + 2 := by exact_mod_cast hrS
  have hi : lowerCritical n 2 = rI := by
    unfold lowerCritical
    apply (Nat.floor_eq_iff (show 0 ≤ E n 2 by unfold E; positivity)).mpr
    unfold E
    norm_num
    constructor <;> linarith
  have hs : upperCritical n 2 = rS := by
    unfold upperCritical
    apply (Nat.ceil_eq_iff (show rS ≠ 0 by omega)).mpr
    rw [Nat.cast_sub hrSpos]
    unfold E
    norm_num
    constructor <;> linarith
  constructor
  · rw [hi]
    exact Nat.sub_sub_self hti
  · rw [hs]
    exact Nat.sub_sub_self (by omega)

/-- Both ambient critical counts coincide at the integral quadratic endpoint. -/
theorem critical_counts_mod_two (ν : ℕ) :
    N (3 * ν + 2) 2 - lowerCritical (3 * ν + 2) 2 = (4 * ν + 2) + ν * (3 * ν + 1) ∧
      N (3 * ν + 2) 2 - upperCritical (3 * ν + 2) 2 = (4 * ν + 2) + ν * (3 * ν + 1) := by
  apply critical_counts_integral
  rw [two_mul_quadratic_count]
  ring

/-- Appending the normal-axis point moves from the ceiling to the floor ideal dimension. -/
theorem critical_counts_mod_one (ν : ℕ) (hν : 2 ≤ ν) :
    N (3 * ν + 1) 2 - lowerCritical (3 * ν + 1) 2 = 4 * ν + ν * (3 * ν - 1) + 1 ∧
      N (3 * ν + 1) 2 - upperCritical (3 * ν + 1) 2 = 4 * ν + ν * (3 * ν - 1) := by
  apply critical_counts_residue_one
  rw [two_mul_quadratic_count]
  have hq : ν * (3 * ν - 1) + ν = 3 * ν * ν := by
    calc
      _ = ν * (3 * ν - 1 + 1) := by ring
      _ = _ := by rw [show 3 * ν - 1 + 1 = 3 * ν by omega]; ring
  nlinarith

variable {K : Type*} [Field K] [CharZero K]

/-- Pass an explicit quadratic configuration to the marked-cone open. -/
theorem idealGenerationAt_of_configuration_middle {n p q : ℕ}
    (C : ConeConfiguration K 2 (n + 1) p q) (hpoint : ∀ i, C.point i ≠ 0)
    (hpost : FullEvaluation C.support (encode C) 2) (hmid : HasMaximalRank (C.middleMultiplication 2))
    (hbalance : (n + 1) * (N (n + 1) 2 - q) = N (n + 1) 3 - q)
    (htrace : IdealGenerationAt K n 2 q) : IdealGenerationAt K (n + 2) 2 (p + q) := by
  have hp : ∀ i, (configuration C.support (encode C)).point i ≠ 0 := by
    rw [configuration_encode]
    exact hpoint
  have hm : HasMaximalRank ((configuration C.support (encode C)).middleMultiplication 2) := by
    rw [configuration_encode]
    exact hmid
  have h := ConeA1Bridge.idealGenerationAt_of_special_middle (by decide : 0 < 2) (by omega)
    C.support (encode C) 2 hp hpost.1 hpost.2.1 hm hbalance htrace
  rwa [show 2 + (n + 1) - 1 = n + 2 by omega] at h

section Configurations

open QuadraticElimination QuadraticFlagFamily QuadraticFlagProbeScalar
open QuadraticCanonicalConeConfiguration QuadraticCoreRestriction
open QuadraticConeResidual QuadraticVariableTransport

omit [CharZero K] in
private theorem encoded_normalEvaluation_surjective {P J : Type*} [Fintype P] [Fintype J]
    {m p q : ℕ} (D : QuadraticLiftParameters K P J) (e : ((P × Bool) ⊕ J) ≃ Fin m)
    (r : ConeIndex P J ≃ Fin p) (C : ConeConfiguration K 2 m p q) (h : Compatible D e r C) :
    Function.Surjective (normalEvaluation C.support (encode C) 2) := by
  intro v
  obtain ⟨f, hf⟩ := normalEval_quadratic_surjective D e r C h v
  refine ⟨f, funext fun i => ?_⟩
  rw [QuadraticTruncatedCone.normalEvaluation_encode_apply]
  exact congrFun hf i

private def firstTwoLayers (l : ℕ) (hl : 2 ≤ l) : Bool → Fin l
  | false => ⟨0, by omega⟩
  | true => ⟨1, by omega⟩

private theorem firstTwoLayers_ne (l : ℕ) (hl : 2 ≤ l) :
    firstTwoLayers l hl false ≠ firstTwoLayers l hl true := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [firstTwoLayers] at hv

/-- The two-normal surjective witness with a selected subfamily of the actual probes. -/
private theorem selected_probe_endpoint {P J : Type*} [Fintype P] [Fintype J] [DecidableEq J]
    (p₀ : P) (layers : Bool → J) (hne : layers false ≠ layers true)
    {n p q s : ℕ}
    (hm : Fintype.card (P × Bool) + Fintype.card J = n + 1)
    (hp : Fintype.card (P × Bool) + 2 * Fintype.card J = p)
    (hq : flagCount (Fintype.card (P × Bool)) (Fintype.card J) + s = q)
    (hselect : s ≤ Fintype.card (P × Bool) + 1)
    (hbalance : (n + 1) * (N (n + 1) 2 - q) = N (n + 1) 3 - q)
    (htrace : IdealGenerationAt K n 2 q) : IdealGenerationAt K (n + 2) 2 (p + q) := by
  classical
  obtain ⟨select⟩ := exists_selectedProbes p₀ s hselect
  let D := parameters K p₀ layers
  let e := variableOrder (P := P) (J := J) hm
  let r := coneOrder (P := P) (J := J) hp
  let k := pointOrder (P := P) (J := J) (E := Fin s) (by simpa only [Fintype.card_fin] using hq)
  let extra : Fin s → (P × Bool) ⊕ J → K := fun i => probePoint p₀ layers (select i)
  let C := QuadraticCanonicalConeConfiguration.configuration D e r k extra
  have hC : Compatible D e r C := configuration_compatible D e r k extra
  have hpost := configuration_fullEvaluation D e r k extra
    (selectedTraceLabelEvaluation_surjective (K := K) p₀ layers hne select)
    (encoded_normalEvaluation_surjective D e r C hC)
  have hpoint (i : Fin p) : C.point i ≠ 0 :=
    C.point_ne_zero i (configuration_normal_ne_zero D e r k extra i)
  have hsurj : Function.Surjective (C.middleMultiplication 2) :=
    QuadraticMiddleEndpoint.canonical_middleMultiplication_surjective e r C p₀ layers select hne hC k
      (configuration_trace D e r k extra) (canonical_configuration_s_ne_zero e r k extra p₀ layers)
  exact idealGenerationAt_of_configuration_middle C hpoint hpost (Or.inr hsurj) hbalance htrace

omit [CharZero K] in
/-- Native first-layer probe labels inherit scalar interpolation from their finite selection. -/
private theorem firstLayer_traceEvaluation_surjective {P J : Type*} [Fintype P] [Fintype J]
    (p₀ : P) (layers : Bool → J) (hne : layers false ≠ layers true) :
    Function.Surjective (traceLabelEvaluation (K := K) (probePoint p₀ layers ∘ firstLayerProbeEmbedding p₀)) := by
  classical
  apply traceLabelEvaluation_surjective
  intro v
  let a : FirstLayerProbeLabel p₀ ≃ Fin (Fintype.card P) :=
    Fintype.equivFinOfCardEq (card_firstLayerProbeLabel p₀)
  let select := firstLayerProbeSelection p₀
  obtain ⟨f, hf⟩ := selectedScalarEvaluation_surjective K p₀ layers hne select (v ∘ a.symm)
  refine ⟨f, ?_⟩
  funext t
  have ht := congrFun hf (a t)
  change eval (probePoint p₀ layers (select (a t))) f.val.val = (v ∘ a.symm) (a t) at ht
  have he : select (a t) = firstLayerProbeEmbedding p₀ t := by
    simp [select, a, firstLayerProbeSelection]
  rw [he] at ht
  change eval (probePoint p₀ layers (firstLayerProbeEmbedding p₀ t)) f.val.val = v t
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using ht

/-- The injective endpoint appends the normal-axis point and uses the native first-layer probes. -/
private theorem firstLayer_probe_endpoint {P J : Type*} [Fintype P] [Fintype J] [DecidableEq J]
    (p₀ : P) (layers : Bool → J) (hne : layers false ≠ layers true)
    {n p q : ℕ}
    (hm : Fintype.card (P × Bool) + Fintype.card J = n + 1)
    (hp : Fintype.card (P × Bool) + 2 * Fintype.card J = p)
    (hq : flagCount (Fintype.card (P × Bool)) (Fintype.card J) + Fintype.card P = q)
    (hbalance : (n + 1) * (N (n + 1) 2 - q) = N (n + 1) 3 - q)
    (htrace : IdealGenerationAt K n 2 q) : IdealGenerationAt K (n + 2) 2 ((p + 1) + q) := by
  classical
  let D := parameters K p₀ layers
  let e := variableOrder (P := P) (J := J) hm
  let r := coneOrder (P := P) (J := J) hp
  let k := pointOrder (P := P) (J := J) (E := FirstLayerProbeLabel p₀)
    (by simpa only [card_firstLayerProbeLabel] using hq)
  let extra : FirstLayerProbeLabel p₀ → (P × Bool) ⊕ J → K :=
    probePoint p₀ layers ∘ firstLayerProbeEmbedding p₀
  let C := QuadraticCanonicalConeConfiguration.configuration D e r k extra
  let qidx := k (.inr (.inl ()))
  let C' := QuadraticTruncatedCone.append C qidx
  have hC : Compatible D e r C := configuration_compatible D e r k extra
  have hpost := configuration_fullEvaluation D e r k extra
    (firstLayer_traceEvaluation_surjective (K := K) p₀ layers hne)
    (encoded_normalEvaluation_surjective D e r C hC)
  have hpoint (i : Fin p) : C.point i ≠ 0 :=
    C.point_ne_zero i (configuration_normal_ne_zero D e r k extra i)
  obtain ⟨f, hf⟩ := QuadraticTruncatedEndpoint.exists_residual_separator
    (e := e) (r := r) (C := C) (D := D) hC qidx
  have hpost' := QuadraticTruncatedCone.fullEvaluation_append C qidx 2 hpoint hpost
    ⟨f, by rw [hf]; exact one_ne_zero⟩
  have hinj : Function.Injective (C'.middleMultiplication 2) :=
    QuadraticTruncatedEndpoint.canonical_truncated_middleMultiplication_injective
      (K := K) (e := e) (r := r) (C := C) (p₀ := p₀) (layers := layers) hne hC k
      (configuration_trace D e r k extra) qidx
  exact idealGenerationAt_of_configuration_middle C'
    (QuadraticTruncatedCone.append_point_ne_zero C qidx hpoint) hpost' (Or.inl hinj) hbalance htrace

end Configurations

/-- The A.2 witness at the integral critical count in `3ν+2` variables. -/
theorem a2_mod_two_endpoint (ν : ℕ) (hν : 2 ≤ ν)
    (htrace : IdealGenerationAt K (3 * ν - 1) 2 (ν * (3 * ν + 1))) :
    IdealGenerationAt K (3 * ν + 1) 2 ((4 * ν + 2) + ν * (3 * ν + 1)) := by
  let p₀ : Fin (ν - 1) := ⟨0, by omega⟩
  let layers := firstTwoLayers (ν + 2) (by omega)
  have hc : Fintype.card (Fin (ν - 1) × Bool) = 2 * (ν - 1) := by
    simp [Fintype.card_prod, Nat.mul_comm]
  have hm : 3 * ν - 1 + 1 = 3 * ν := by omega
  have h : IdealGenerationAt K ((3 * ν - 1) + 2) 2 ((4 * ν + 2) + ν * (3 * ν + 1)) := by
    refine selected_probe_endpoint p₀ layers (firstTwoLayers_ne _ _) (p := 4 * ν + 2)
      (s := 2 * (ν - 1) + 1)
      ?_ ?_ ?_ ?_ ?_ htrace
    · rw [hc, Fintype.card_fin]
      omega
    · rw [hc, Fintype.card_fin]
      omega
    · rw [hc, Fintype.card_fin]
      exact flag_count_mod_two ν hν
    · rw [hc]
    · simpa only [hm] using trace_balance_mod_two ν hν
  simpa only [show 3 * ν - 1 + 2 = 3 * ν + 1 by omega] using h

/-- The A.2 witness at the ceiling ideal dimension in `3ν+1` variables. -/
theorem a2_mod_one_endpoint (ν : ℕ) (hν : 2 ≤ ν)
    (htrace : IdealGenerationAt K (3 * ν - 2) 2 (ν * (3 * ν - 1))) :
    IdealGenerationAt K (3 * ν) 2 (4 * ν + ν * (3 * ν - 1)) := by
  let p₀ : Fin (ν - 1) := ⟨0, by omega⟩
  let layers := firstTwoLayers (ν + 1) (by omega)
  have hc : Fintype.card (Fin (ν - 1) × Bool) = 2 * (ν - 1) := by
    simp [Fintype.card_prod, Nat.mul_comm]
  have hm : 3 * ν - 2 + 1 = 3 * ν - 1 := by omega
  have h : IdealGenerationAt K ((3 * ν - 2) + 2) 2 (4 * ν + ν * (3 * ν - 1)) := by
    refine selected_probe_endpoint p₀ layers (firstTwoLayers_ne _ _) (p := 4 * ν) (s := ν - 1)
      ?_ ?_ ?_ ?_ ?_ htrace
    · rw [hc, Fintype.card_fin]
      omega
    · rw [hc, Fintype.card_fin]
      omega
    · rw [hc, Fintype.card_fin]
      exact flag_count_mod_one ν hν
    · rw [hc]
      omega
    · simpa only [hm] using trace_balance_mod_one ν hν
  simpa only [show 3 * ν - 2 + 2 = 3 * ν by omega] using h

/-- The A.3 witness at the floor ideal dimension in `3ν+1` variables. -/
theorem a3_mod_one_endpoint (ν : ℕ) (hν : 2 ≤ ν)
    (htrace : IdealGenerationAt K (3 * ν - 2) 2 (ν * (3 * ν - 1))) :
    IdealGenerationAt K (3 * ν) 2 (4 * ν + ν * (3 * ν - 1) + 1) := by
  let p₀ : Fin (ν - 1) := ⟨0, by omega⟩
  let layers := firstTwoLayers (ν + 1) (by omega)
  have hc : Fintype.card (Fin (ν - 1) × Bool) = 2 * (ν - 1) := by
    simp [Fintype.card_prod, Nat.mul_comm]
  have hm : 3 * ν - 2 + 1 = 3 * ν - 1 := by omega
  have h : IdealGenerationAt K ((3 * ν - 2) + 2) 2 ((4 * ν + 1) + ν * (3 * ν - 1)) := by
    refine firstLayer_probe_endpoint p₀ layers (firstTwoLayers_ne _ _) (p := 4 * ν)
      ?_ ?_ ?_ ?_ htrace
    · rw [hc, Fintype.card_fin]
      omega
    · rw [hc, Fintype.card_fin]
      omega
    · rw [hc, Fintype.card_fin, Fintype.card_fin]
      exact flag_count_mod_one ν hν
    · simpa only [hm] using trace_balance_mod_one ν hν
  rw [show 3 * ν - 2 + 2 = 3 * ν by omega,
    show (4 * ν + 1) + ν * (3 * ν - 1) = 4 * ν + ν * (3 * ν - 1) + 1 by omega] at h
  exact h

/-- The two-normal step in `3ν+2` homogeneous variables. -/
theorem quadratic_mod_two_all (ν : ℕ) (hν : 2 ≤ ν)
    (htrace : IdealGenerationAt K (3 * ν - 1) 2 (ν * (3 * ν + 1))) :
    ∀ p, IdealGenerationAt K (3 * ν + 1) 2 p := by
  have h := a2_mod_two_endpoint ν hν htrace
  apply idealGenerationAt_all_of_critical (by omega) (by decide)
  · rw [show 3 * ν + 1 + 1 = 3 * ν + 2 by omega, (critical_counts_mod_two ν).1]
    exact h
  · rw [show 3 * ν + 1 + 1 = 3 * ν + 2 by omega, (critical_counts_mod_two ν).2]
    exact h

/-- The two-normal step in `3ν+1` homogeneous variables. -/
theorem quadratic_mod_one_all (ν : ℕ) (hν : 2 ≤ ν)
    (htrace : IdealGenerationAt K (3 * ν - 2) 2 (ν * (3 * ν - 1))) :
    ∀ p, IdealGenerationAt K (3 * ν) 2 p := by
  apply idealGenerationAt_all_of_critical (by omega) (by decide)
  · rw [(critical_counts_mod_one ν hν).1]
    exact a3_mod_one_endpoint ν hν htrace
  · rw [(critical_counts_mod_one ν hν).2]
    exact a2_mod_one_endpoint ν hν htrace

end IdealGeneration.QuadraticEndpointA1
