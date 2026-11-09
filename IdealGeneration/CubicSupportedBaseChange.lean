module

public import IdealGeneration.CubicSupportedConfiguration
public import IdealGeneration.ConeJointMatrix
public import IdealGeneration.QuadraticTraceRestriction
public import IdealGeneration.GenericRectangularDescent

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual supported cubic middle map under rational coefficient extension. -/

noncomputable section

namespace IdealGeneration.CubicSupported.Parameters

variable {m f : ℕ} (P : Parameters ℚ m)
variable (K : Type*) [Field K] [CharZero K]

/-- Realize rational primitive cone data over a characteristic-zero field. -/
def castRat : Parameters K m where
  single := P.single
  vertexSlope i d := P.vertexSlope i d
  vertexHeight i d := P.vertexHeight i d
  edgeSlope e d := P.edgeSlope e d
  edgeHeight e d := P.edgeHeight e d
  edgeLambda e := P.edgeLambda e
  vertexSlope_ne i := fun h => P.vertexSlope_ne i ((Rat.castHom K).injective h)
  vertexHeight_ne i d := fun h => P.vertexHeight_ne i d ((Rat.castHom K).injective (by simpa using h))
  edgeSlope_ne e he := fun h => P.edgeSlope_ne e he ((Rat.castHom K).injective h)
  edgeHeight_ne e d := fun h => P.edgeHeight_ne e d ((Rat.castHom K).injective (by simpa using h))
  edgeLambda_ne e := fun h => P.edgeLambda_ne e ((Rat.castHom K).injective (by simpa using h))

@[simp] theorem castRat_single (e : Edge m) : (P.castRat K).single e = P.single e := rfl

variable (free : Fin f → Fin m → ℚ)

private theorem castRat_traceRepresentative (a : TraceLabel m f) (j : Fin m) :
    (P.castRat K).traceRepresentative (fun i j => (free i j : K)) a j =
      (P.traceRepresentative free a j : K) := by
  rcases a with (i | e) | i
  · by_cases hj : j = i <;> simp [traceRepresentative, vertexSupport, hj]
  · have hne := ne_of_lt e.property
    by_cases h1 : j = e.val.1 <;> by_cases h2 : j = e.val.2 <;>
      simp [traceRepresentative, edgeSupport, vertexSupport, castRat, h1, h2, hne, Ne.symm hne]
  · rfl

private theorem castRat_coneNormal (a : P.ConeLabel) (d : Fin 2) :
    (P.castRat K).coneNormal a d = (P.coneNormal a d : K) := by
  rcases a with ⟨i, k⟩ | a <;> fin_cases d <;> simp [coneNormal, castRat]

private theorem castRat_coneHeight (a : P.ConeLabel) :
    (P.castRat K).coneHeight a = (P.coneHeight a : K) := by
  cases a <;> rfl

/-- Trace representatives commute with the field map. -/
theorem castRat_trace (i : Fin (Fintype.card (TraceLabel m f))) (j : Fin m) :
    ((P.castRat K).toConeConfiguration (fun i j => (free i j : K))).trace i j =
      ((P.toConeConfiguration free).trace i j : K) :=
  P.castRat_traceRepresentative K free ((traceLabelEquiv m f).symm i) j

/-- Normal coordinates commute with the field map. -/
theorem castRat_normal (i : Fin (Fintype.card P.ConeLabel)) (d : Fin 2) :
    ((P.castRat K).toConeConfiguration (fun i j => (free i j : K))).normal i d =
      ((P.toConeConfiguration free).normal i d : K) :=
  P.castRat_coneNormal K (P.coneLabelEquiv.symm i) d

/-- Cone heights commute with the field map. -/
theorem castRat_height (i : Fin (Fintype.card P.ConeLabel)) :
    ((P.castRat K).toConeConfiguration (fun i j => (free i j : K))).height i =
      ((P.toConeConfiguration free).height i : K) :=
  P.castRat_coneHeight K (P.coneLabelEquiv.symm i)

/-- Attached support labels are unchanged by extending the scalar field. -/
theorem castRat_support (i : Fin (Fintype.card P.ConeLabel)) :
    ((P.castRat K).toConeConfiguration (fun i j => (free i j : K))).support i =
      (P.toConeConfiguration free).support i := by
  change traceLabelEquiv m f ((P.castRat K).coneSupportLabel (P.coneLabelEquiv.symm i)) =
    traceLabelEquiv m f (P.coneSupportLabel (P.coneLabelEquiv.symm i))
  congr 1
  cases P.coneLabelEquiv.symm i <;> rfl

/-- Actual marked cone points are the coordinatewise rational casts. -/
theorem castRat_point (i : Fin (Fintype.card P.ConeLabel)) (j : Fin (2 + m)) :
    ((P.castRat K).toConeConfiguration (fun i j => (free i j : K))).point i j =
      ((P.toConeConfiguration free).point i j : K) := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simpa only [ConeConfiguration.point, Fin.addCases_left] using P.castRat_normal K free i k
  · simp only [ConeConfiguration.point, Fin.addCases_right, P.castRat_height K free i,
      P.castRat_support K free i, P.castRat_trace K free, Rat.cast_mul]

end IdealGeneration.CubicSupported.Parameters

namespace IdealGeneration.ConeMonomialChart
open MvPolynomial Matrix

/-- Injectivity of the native middle map implies injectivity of the full coefficient stack. -/
theorem jointMatrix_injective_of_middle {K : Type*} [Field K] {c m p q d : ℕ}
    {ν τ o : Type*} [Fintype ν] [Fintype τ] [DecidableEq ν] [DecidableEq τ]
    (C : ConeConfiguration K c m p q)
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ)
    (hnd : ∀ i, (en i).degree = d) (htd : ∀ i, (et i).degree = d)
    (hnn : ∀ i, ∃ j : Fin c, en i (j.castAdd m) ≠ 0)
    (hne : Function.Injective en) (hte : Function.Injective et)
    (hout : ∀ e : Fin (c + m) →₀ ℕ, e.degree = d + 1 → ∃ i, out i = e)
    (hm : Function.Injective (C.middleMultiplication d)) :
    Function.Injective
      (jointMatrix en et out (evaluationMatrix C.point en) (evaluationMatrix C.trace et)).mulVec := by
  let En := evaluationMatrix C.point en
  let Et := evaluationMatrix C.trace et
  let A := jointMatrix en et out En Et
  suffices hz : ∀ x, A.mulVec x = 0 → x = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [Matrix.mulVec_sub, hxy, sub_self]
  intro x hx
  let xn (j : Fin (c + m)) : ν → K := fun a => x (.inl (j, a))
  let xt (j : Fin c) : τ → K := fun a => x (.inr (j, a))
  have hn (j : Fin (c + m)) (i : Fin p) : eval (C.point i) (synth en (xn j)) = 0 := by
    have h := congrFun hx (.inl (.inl (j, i)))
    change (jointEvaluation En Et).mulVec x (.inl (j, i)) = 0 at h
    rw [jointEvaluation_mulVec_normal] at h
    rw [evaluationMatrix_mulVec]
    exact h
  have ht (j : Fin c) (i : Fin q) : eval (C.trace i) (synth et (xt j)) = 0 := by
    have h := congrFun hx (.inl (.inr (j, i)))
    change (jointEvaluation En Et).mulVec x (.inr (j, i)) = 0 at h
    rw [jointEvaluation_mulVec_trace] at h
    rw [evaluationMatrix_mulVec]
    exact h
  let f : ConeMiddleFamily.NativeSource C d :=
    (fun j => ⟨(normalSynth en hnd hnn (xn j)).val,
      ⟨(C.mem_conePiece _).mpr (hn j), (normalSynth en hnd hnn (xn j)).property⟩⟩,
      fun j => ⟨formSynth et htd (xt j), (C.mem_tracePiece _).mpr (ht j)⟩)
  have htail : (∑ j : Fin (c + m), X j * (C.normalTraceCoefficients d f.2 j).val) =
      ∑ j : Fin c, X (j.castAdd m) * coneExtend K c m (synth et (xt j)) := by
    rw [Fin.sum_univ_add]
    simp [ConeConfiguration.normalTraceCoefficients, coneExtendForm, f, formSynth]
  have hcoeff (i : o) : (C.middleMultiplication d f).val.val.coeff (out i) = 0 := by
    have h := congrFun hx (.inr i)
    change (middleMatrix en et out (1 : Matrix ν ν K) (1 : Matrix τ τ K)).mulVec x i = 0 at h
    rw [middleMatrix_mulVec] at h
    simp only [Matrix.one_mulVec] at h
    rw [C.middleMultiplication_val]
    simp only [Submodule.coe_add, formMultiplication_val]
    rw [htail]
    exact h
  have hprod : C.middleMultiplication d f = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    apply MvPolynomial.ext
    intro e
    change (C.middleMultiplication d f).val.val.coeff e = 0
    by_cases he : e.degree = d + 1
    · obtain ⟨i, rfl⟩ := hout e he
      exact hcoeff i
    · exact (C.middleMultiplication d f).val.property.coeff_eq_zero he
  have hf : f = 0 := hm (hprod.trans (map_zero _).symm)
  funext i
  cases i with
  | inl i =>
    have h := congrArg (fun f : ConeMiddleFamily.NativeSource C d => (f.1 i.1).val.val) hf
    change synth en (xn i.1) = 0 at h
    have he : xn i.1 = 0 := synth_injective en hne (h.trans (map_zero _).symm)
    exact congrFun he i.2
  | inr i =>
    have h := congrArg (fun f : ConeMiddleFamily.NativeSource C d => (f.2 i.1).val.val) hf
    change synth et (xt i.1) = 0 at h
    have he : xt i.1 = 0 := synth_injective et hte (h.trans (map_zero _).symm)
    exact congrFun he i.2

end IdealGeneration.ConeMonomialChart

namespace IdealGeneration.CubicSupported.BaseChange

open MvPolynomial ConeMonomialChart

variable {K : Type*} [Field K] {n c m d : ℕ}

private abbrev HomExp (n d : ℕ) := {u : Fin n →₀ ℕ // u.degree = d}
private abbrev NormalExp (c m d : ℕ) :=
  {u : Fin (c + m) →₀ ℕ // u.degree = d ∧ ∃ j : Fin c, u (j.castAdd m) ≠ 0}

private instance (n d : ℕ) : Fintype (HomExp n d) :=
  (Finsupp.finite_of_degree_eq (σ := Fin n) d).fintype

private instance (c m d : ℕ) : Fintype (NormalExp c m d) :=
  ((Finsupp.finite_of_degree_eq (σ := Fin (c + m)) d).subset (fun _ h => h.1)).fintype

private theorem synth_subtype_coeff (p : Poly K n) (s : (Fin n →₀ ℕ) → Prop)
    [Fintype (Subtype s)] (hs : ∀ u, p.coeff u ≠ 0 → s u) :
    synth (fun u : Subtype s => u.val) (fun u => p.coeff u.val) = p := by
  classical
  apply MvPolynomial.ext
  intro u
  rw [synth_apply, coeff_sum]
  by_cases hu : s u
  · rw [Finset.sum_eq_single (⟨u, hu⟩ : Subtype s)]
    · simp
    · intro a _ ha
      have hn : a.val ≠ u := fun h => ha (Subtype.ext h)
      simp [hn]
    · simp
  · rw [show p.coeff u = 0 from by by_contra h; exact hu (hs u h)]
    apply Finset.sum_eq_zero
    intro a _
    have hn : a.val ≠ u := fun h => hu (h ▸ a.property)
    simp [hn]

private theorem degree_of_coeff_ne_zero (p : Forms K n d) {u : Fin n →₀ ℕ}
    (hu : p.val.coeff u ≠ 0) : u.degree = d := by
  rw [Finsupp.degree_eq_weight_one]
  exact p.property hu

private theorem formSynth_homExp_surjective :
    Function.Surjective (formSynth (K := K) (fun u : HomExp n d => u.val) (fun u => u.property)) := by
  intro p
  refine ⟨fun u => p.val.coeff u.val, Subtype.ext ?_⟩
  exact synth_subtype_coeff p.val _ (fun _ h => degree_of_coeff_ne_zero p h)

private theorem coneRestrict_eq_killCompl :
    coneRestrict K c m = MvPolynomial.killCompl (Fin.natAddEmb c : Fin m ↪ Fin (c + m)).injective := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [coneRestrict_X_normal]
    symm
    apply QuadraticTraceRestriction.restrict_X_off K (Fin.natAddEmb c)
    rintro ⟨a, ha⟩
    have h := congrArg Fin.val ha
    change c + a.val = j.val at h
    omega
  · rw [coneRestrict_X_trace]
    exact (QuadraticTraceRestriction.restrict_X_embedded K (Fin.natAddEmb c) j).symm

private theorem normal_exp_of_coeff_ne_zero (p : ConeMiddleFamily.normalForms K c m d)
    {u : Fin (c + m) →₀ ℕ} (hu : p.val.val.coeff u ≠ 0) :
    ∃ j : Fin c, u (j.castAdd m) ≠ 0 := by
  by_contra h
  have hzero (j : Fin c) : u (j.castAdd m) = 0 := by
    by_contra hn
    exact h ⟨j, hn⟩
  let e : Fin m ↪ Fin (c + m) := Fin.natAddEmb c
  have hs : ↑u.support ⊆ Set.range e := by
    intro j
    refine Fin.addCases (fun i hi => ?_) (fun i _ => ⟨i, rfl⟩) j
    exact False.elim ((Finsupp.mem_support_iff.mp hi) (hzero i))
  let v := u.comapDomain e e.injective.injOn
  have hv : v.mapDomain e = u := Finsupp.mapDomain_comapDomain e e.injective u hs
  have hp : coneRestrict K c m p.val.val = 0 := congrArg Subtype.val p.property
  rw [coneRestrict_eq_killCompl] at hp
  have he : (MvPolynomial.killCompl e.injective p.val.val).coeff v = 0 := by
    change _ = (0 : Poly K m).coeff v
    exact congrArg (fun f : Poly K m => f.coeff v) hp
  rw [MvPolynomial.coeff_killCompl, hv] at he
  exact hu he

private theorem normalSynth_normalExp_surjective :
    Function.Surjective (normalSynth (K := K) (fun u : NormalExp c m d => u.val)
      (fun u => u.property.1) (fun u => u.property.2)) := by
  intro p
  refine ⟨fun u => p.val.val.coeff u.val, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact synth_subtype_coeff p.val.val _ (fun _ h =>
    ⟨degree_of_coeff_ne_zero p.val h, normal_exp_of_coeff_ne_zero p h⟩)

private theorem rat_mulVec_injective {ι κ : Type*} [Fintype ι] [Fintype κ] [CharZero K]
    (A : Matrix ι κ ℚ) (hi : Function.Injective A.mulVec) :
    Function.Injective (A.map (Rat.castHom K)).mulVec := by
  classical
  let F := A.mulVecLin
  have hF : Function.Injective F := hi
  obtain ⟨L, hL⟩ := F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hF)
  let B : Matrix κ ι ℚ := LinearMap.toMatrix' L
  have hleft : B * A = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    change (Matrix.toLin' (LinearMap.toMatrix' L)).comp F = LinearMap.id
    rw [Matrix.toLin'_toMatrix']
    exact hL
  have hcast : B.map (Rat.castHom K) * A.map (Rat.castHom K) = 1 := by
    rw [← Matrix.map_mul, hleft, Matrix.map_one _ (map_zero _) (map_one _)]
  intro x y hxy
  have h := congrArg (B.map (Rat.castHom K)).mulVec hxy
  simpa only [Matrix.mulVec_mulVec, hcast, Matrix.one_mulVec] using h


variable [CharZero K] {f : ℕ}

/-- Injectivity of the actual rational supported middle map survives coefficient extension. -/
theorem supportedMiddle_cast_injective (P : Parameters ℚ m) (free : Fin f → Fin m → ℚ)
    (hm : Function.Injective ((P.toConeConfiguration free).middleMultiplication 3)) :
    Function.Injective
      (((P.castRat K).toConeConfiguration (fun i j => (free i j : K))).middleMultiplication 3) := by
  classical
  let en : NormalExp 2 m 3 → Fin (2 + m) →₀ ℕ := Subtype.val
  let et : HomExp m 3 → Fin m →₀ ℕ := Subtype.val
  let out : HomExp (2 + m) 4 → Fin (2 + m) →₀ ℕ := Subtype.val
  have hnd : ∀ i, (en i).degree = 3 := fun i => i.property.1
  have htd : ∀ i, (et i).degree = 3 := fun i => i.property
  have hnn : ∀ i, ∃ j : Fin 2, en i (j.castAdd m) ≠ 0 := fun i => i.property.2
  let C₀ := P.toConeConfiguration free
  let C₁ := (P.castRat K).toConeConfiguration (fun i j => (free i j : K))
  let A := jointMatrix en et out (evaluationMatrix C₀.point en) (evaluationMatrix C₀.trace et)
  have hA : Function.Injective A.mulVec :=
    jointMatrix_injective_of_middle C₀ en et out hnd htd hnn Subtype.val_injective
      Subtype.val_injective (fun e he => ⟨⟨e, he⟩, rfl⟩) hm
  have hPoint : (fun i j => Rat.castHom K (C₀.point i j)) = C₁.point := by
    funext i j
    exact (P.castRat_point K free i j).symm
  have hTrace : (fun i j => Rat.castHom K (C₀.trace i j)) = C₁.trace := by
    funext i j
    exact (P.castRat_trace K free i j).symm
  have hmap : A.map (Rat.castHom K) =
      jointMatrix en et out (evaluationMatrix C₁.point en) (evaluationMatrix C₁.trace et) := by
    dsimp only [A]
    rw [jointMatrix_map, evaluationMatrix_map, evaluationMatrix_map, hPoint, hTrace]
    rfl
  refine middle_injective_of_jointMatrix C₁ en et out hnd htd hnn
    normalSynth_normalExp_surjective formSynth_homExp_surjective ?_
  rw [← hmap]
  exact rat_mulVec_injective A hA

/-- Rational supported witnesses give supported witnesses over any characteristic-zero field. -/
theorem exists_rational_supported_middle_to_charZero (single : Edge m → Bool)
    (h : ∃ (P : Parameters ℚ m) (free : Fin f → Fin m → ℚ),
      (∀ e, P.single e = single e) ∧
      Function.Injective ((P.toConeConfiguration free).middleMultiplication 3)) :
    ∃ (P : Parameters K m) (free : Fin f → Fin m → K),
      (∀ e, P.single e = single e) ∧
      Function.Injective ((P.toConeConfiguration free).middleMultiplication 3) := by
  obtain ⟨P, free, hgraph, hm⟩ := h
  exact ⟨P.castRat K, fun i j => (free i j : K), hgraph,
    supportedMiddle_cast_injective P free hm⟩

end IdealGeneration.CubicSupported.BaseChange
