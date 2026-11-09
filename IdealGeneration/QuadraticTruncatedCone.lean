module

public import IdealGeneration.ConeMiddleOpen
public import IdealGeneration.QuadraticVariableTransport

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Adding the first normal coordinate point to a quadratic cone

The trace configuration is unchanged. The appended point imposes one extra
scalar equation on the residual forms, and the resulting middle map is the
restriction of the original middle map.
-/

noncomputable section
namespace IdealGeneration.QuadraticTruncatedCone
open MvPolynomial ConeParameterSpace ConeMiddleFamily QuadraticVariableTransport

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {m p q : ℕ}
variable (C : ConeConfiguration K 2 m p q) (qidx : Fin q)

/-- The appended representative has first normal coordinate one and all
other coordinates zero. Its marked support does not affect the representative. -/
def append : ConeConfiguration K 2 m (p + 1) q where
  trace := C.trace
  normal := Fin.snoc C.normal (fun i => if finTwoEquiv i then 0 else 1)
  support := Fin.snoc C.support qidx
  height := Fin.snoc C.height 0

@[simp] theorem append_trace : (append C qidx).trace = C.trace := rfl

@[simp] theorem append_tracePiece (d : ℕ) :
    (append C qidx).tracePiece d = C.tracePiece d := rfl

@[simp] theorem append_support_castSucc (i : Fin p) :
    (append C qidx).support i.castSucc = C.support i := by
  simp [append]

@[simp] theorem append_support_last :
    (append C qidx).support (Fin.last p) = qidx := by
  simp [append]

@[simp] theorem append_normal_castSucc (i : Fin p) :
    (append C qidx).normal i.castSucc = C.normal i := by
  simp [append]

@[simp] theorem append_normal_last :
    (append C qidx).normal (Fin.last p) = fun j => if finTwoEquiv j then 0 else 1 := by
  simp [append]

@[simp] theorem append_height_castSucc (i : Fin p) :
    (append C qidx).height i.castSucc = C.height i := by
  simp [append]

@[simp] theorem append_height_last :
    (append C qidx).height (Fin.last p) = 0 := by
  simp [append]

/-- The enlarged marked support is injective if the appended label was unused. -/
theorem append_support_injective
    (h : Function.Injective C.support) (hfresh : ∀ i, C.support i ≠ qidx) :
    Function.Injective (append C qidx).support := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · exact fun _ => rfl
  · simp only [append_support_last, append_support_castSucc]
    exact fun hj => (hfresh j hj.symm).elim
  · simp only [append_support_last, append_support_castSucc]
    exact fun hi => (hfresh i hi).elim
  · simp only [append_support_castSucc]
    exact fun hij => congrArg Fin.castSucc (h hij)

@[simp] theorem append_point_castSucc (i : Fin p) :
    (append C qidx).point i.castSucc = C.point i := by
  unfold ConeConfiguration.point
  rw [append_normal_castSucc, append_height_castSucc, append_trace, append_support_castSucc]

/-- In any trace variable ordering, the last point is the first normal axis. -/
theorem append_point_last {T : Type*} (e : T ≃ Fin m) :
    (append C qidx).point (Fin.last p) =
      pointOf e (fun b => if b then 0 else 1) (0 : T → K) := by
  unfold ConeConfiguration.point pointOf
  rw [append_normal_last, append_height_last]
  simp only [zero_mul]; rfl

/-- The new cone normal is nonzero. -/
theorem append_point_last_ne_zero :
    (append C qidx).point (Fin.last p) ≠ 0 := by
  apply (append C qidx).point_ne_zero
  intro h
  have hv := congrFun h (finTwoEquiv.symm false)
  simp at hv

/-- All enlarged representatives off the trace are nonzero when the old ones are. -/
theorem append_point_ne_zero (h : ∀ i, C.point i ≠ 0) :
    ∀ i, (append C qidx).point i ≠ 0 := by
  intro i
  refine Fin.lastCases (append_point_last_ne_zero C qidx) (fun j => ?_) i
  simpa only [append_point_castSucc] using h j

/-- The appended point's scalar evaluation on the old residual space. -/
def extraEvaluation (d : ℕ) : C.residualPiece d →ₗ[K] K :=
  (evaluationLinear K (2 + m) d ((append C qidx).point (Fin.last p))).comp
    (C.residualPiece d).subtype

@[simp] theorem extraEvaluation_apply (d : ℕ) (f : C.residualPiece d) :
    extraEvaluation C qidx d f =
      eval ((append C qidx).point (Fin.last p)) f.val.val := rfl

/-- The only additional residual condition is vanishing at the appended point. -/
theorem mem_residualPiece_append_iff (d : ℕ) (f : Forms K (2 + m) d) :
    f ∈ (append C qidx).residualPiece d ↔
      f ∈ C.residualPiece d ∧ eval ((append C qidx).point (Fin.last p)) f.val = 0 := by
  constructor
  · intro h
    refine ⟨⟨(C.mem_conePiece f).mpr (fun i => ?_), h.2⟩,
      ((append C qidx).mem_conePiece f).mp h.1 (Fin.last p)⟩
    simpa only [append_point_castSucc] using
      ((append C qidx).mem_conePiece f).mp h.1 i.castSucc
  · rintro ⟨h, hl⟩
    refine ⟨((append C qidx).mem_conePiece f).mpr (fun i => ?_), h.2⟩
    refine Fin.lastCases hl (fun j => ?_) i
    simpa only [append_point_castSucc] using (C.mem_conePiece f).mp h.1 j

/-- Forget the appended vanishing condition. -/
def residualInclusion (d : ℕ) :
    (append C qidx).residualPiece d →ₗ[K] C.residualPiece d :=
  Submodule.inclusion fun f hf => ((mem_residualPiece_append_iff C qidx d f).mp hf).1

@[simp] theorem residualInclusion_val (d : ℕ) (f : (append C qidx).residualPiece d) :
    (residualInclusion C qidx d f).val = f.val := rfl

theorem residualInclusion_injective (d : ℕ) :
    Function.Injective (residualInclusion C qidx d) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun z : C.residualPiece d => z.val) h

/-- The new residual space is the kernel of the additional evaluation. -/
def residualToKernelEquiv (d : ℕ) :
    (append C qidx).residualPiece d ≃ₗ[K] (extraEvaluation C qidx d).ker where
  toFun f := ⟨residualInclusion C qidx d f,
    ((mem_residualPiece_append_iff C qidx d f.val).mp f.property).2⟩
  invFun f := ⟨f.val.val, (mem_residualPiece_append_iff C qidx d f.val.val).mpr
    ⟨f.val.property, f.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Keep the trace coefficients and forget the extra residual condition in
each of the ambient coordinate directions. -/
def middleSourceInclusion (d : ℕ) :
    NativeSource (append C qidx) d →ₗ[K] NativeSource C d :=
  (LinearMap.pi (fun i =>
    (residualInclusion C qidx d).comp (LinearMap.proj i))).prodMap
    (LinearMap.id : (Fin 2 → C.tracePiece d) →ₗ[K] (Fin 2 → C.tracePiece d))

@[simp] theorem middleSourceInclusion_apply (d : ℕ) (x : NativeSource (append C qidx) d) :
    middleSourceInclusion C qidx d x = (fun i => residualInclusion C qidx d (x.1 i), x.2) :=
  rfl

theorem middleSourceInclusion_injective (d : ℕ) :
    Function.Injective (middleSourceInclusion C qidx d) := by
  intro x y h
  apply Prod.ext
  · funext i
    exact residualInclusion_injective C qidx d (congrFun (congrArg Prod.fst h) i)
  · exact congrArg (fun z : NativeSource C d => z.2) h

/-- The actual middle maps commute with forgetting the appended condition. -/
theorem middleMultiplication_covariance (d : ℕ) (x : NativeSource (append C qidx) d) :
    residualInclusion C qidx (d + 1) ((append C qidx).middleMultiplication d x) =
      C.middleMultiplication d (middleSourceInclusion C qidx d x) := by
  apply Subtype.ext
  rfl

/-- In encoded coordinates, normal-form evaluation is evaluation at the
actual marked cone representatives. -/
theorem normalEvaluation_encode_apply {s : ℕ} (B : ConeConfiguration K 2 m s q)
    (d : ℕ) (f : normalForms K 2 m d) (i : Fin s) :
    normalEvaluation B.support (encode B) d f i = eval (B.point i) f.val.val := by
  change eval ((configuration B.support (encode B)).point i) f.val.val = _
  rw [configuration_encode]

/-- An old residual separator allows the new cone evaluation to prescribe
one more independent scalar value. -/
theorem normalEvaluation_append_surjective (d : ℕ)
    (hOld : Function.Surjective (normalEvaluation C.support (encode C) d))
    (hSep : ∃ f : C.residualPiece d,
      eval ((append C qidx).point (Fin.last p)) f.val.val ≠ 0) :
    Function.Surjective (normalEvaluation (append C qidx).support (encode (append C qidx)) d) := by
  intro v
  obtain ⟨f, hf⟩ := hOld (fun i => v i.castSucc)
  obtain ⟨g, hg⟩ := hSep
  let G : normalForms K 2 m d := ⟨g.val, g.property.2⟩
  let y := (append C qidx).point (Fin.last p)
  let c := (v (Fin.last p) - eval y f.val.val) / eval y g.val.val
  refine ⟨f + c • G, ?_⟩
  rw [map_add, map_smul]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change normalEvaluation (append C qidx).support (encode (append C qidx)) d f (Fin.last p) +
      c * normalEvaluation (append C qidx).support (encode (append C qidx)) d G (Fin.last p) =
        v (Fin.last p)
    rw [normalEvaluation_encode_apply, normalEvaluation_encode_apply]
    change eval y f.val.val + ((v (Fin.last p) - eval y f.val.val) / eval y g.val.val) *
      eval y g.val.val = v (Fin.last p)
    rw [div_mul_cancel₀ _ hg]
    ring
  · change normalEvaluation (append C qidx).support (encode (append C qidx)) d f j.castSucc +
      c * normalEvaluation (append C qidx).support (encode (append C qidx)) d G j.castSucc =
        v j.castSucc
    rw [normalEvaluation_encode_apply, normalEvaluation_encode_apply, append_point_castSucc]
    change eval (C.point j) f.val.val + c * eval (C.point j) g.val.val = v j.castSucc
    rw [(C.mem_conePiece g.val).mp g.property.1 j, mul_zero, add_zero]
    rw [← normalEvaluation_encode_apply]
    exact congrFun hf j

/-- The new configuration satisfies the scalar postulation hypotheses of the
middle-rank open, with the same trace scalar evaluation as before. -/
theorem fullEvaluation_append (d : ℕ)
    (hpoint : ∀ i, C.point i ≠ 0)
    (hOld : FullEvaluation C.support (encode C) d)
    (hSep : ∃ f : C.residualPiece d,
      eval ((append C qidx).point (Fin.last p)) f.val.val ≠ 0) :
    FullEvaluation (append C qidx).support (encode (append C qidx)) d := by
  apply fullEvaluation_of_degree
  · intro i
    rw [configuration_encode]
    exact append_point_ne_zero C qidx hpoint i
  · exact normalEvaluation_append_surjective C qidx d hOld.1 hSep
  · exact hOld.2.1

end IdealGeneration.QuadraticTruncatedCone
