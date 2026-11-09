module

public import IdealGeneration.TwoNormalIntegral
public import IdealGeneration.TwoNormalMotion

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Maximal rank for the marked two-normal motion

The fixed groups retain their evaluation map. On the trace, the fixed-fiber
remainder has precisely the two normal coordinate responses. This joins the
geometric kernel and cokernel identifications to the deformation theorem.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial TwoNormalSlice TwoNormalTrace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m d p : ℕ}

abbrev AmbientEuler (K : Type*) [Field K] (m d : ℕ) :=
  HyperplaneEuler.Relations K (m + 2) (d + 1 + 1)

abbrev NormalCoefficients (K : Type*) [Field K] (m d : ℕ) :=
  (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)

local instance markedEulerGroup : AddCommGroup (AmbientEuler K m d) :=
  Module.addCommMonoidToAddCommGroup K

/-- The scalar trace of the coefficient of the second normal in `F_s`. -/
def normalSCoefficient (y : Fin m → K) : NormalCoefficients K m d →ₗ[K] K :=
  ((evaluationLinear K m (d + 1) y).comp (restrictTraceForm K m (d + 1))).comp
    (LinearMap.snd K (Fin m → Forms K (m + 2) d) (Forms K (m + 2) (d + 1)))

/-- The scalar trace of the coefficient of the first normal in `F_t`. -/
def normalTCoefficient (y : Fin m → K) : NormalCoefficients K m d →ₗ[K] K :=
  ((evaluationLinear K m (d + 1) y).comp (restrictTraceForm K m (d + 1))).comp
    (-(LinearMap.snd K (Fin m → Forms K (m + 2) d) (Forms K (m + 2) (d + 1))) -
      (tangentProduct K m d).comp
        (LinearMap.fst K (Fin m → Forms K (m + 2) d) (Forms K (m + 2) (d + 1))))

section Marked
variable {W QA QB : Type*}
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup QA] [Module K QA] [FiniteDimensional K QA]
  [AddCommGroup QB] [Module K QB] [FiniteDimensional K QB]

/-- Euler evaluation at the marked special configuration in fixed fibers. -/
def markedBaseEvaluation (E : AmbientEuler K m d →ₗ[K] W)
    (y : Fin p → Fin m → K)
    (I : TraceFibers (fun i => commonTracePoint (y i)) →ₗ[K] W) :
    AmbientEuler K m d →ₗ[K] W :=
  E + I.comp (traceFiberEvaluation (fun i => commonTracePoint (y i)) (d + 1 + 1))

/-- Move the common trace points in the two normals and keep the other groups fixed. -/
def markedMovingEvaluation (E : AmbientEuler K m d →ₗ[K] W)
    (y : Fin p → Fin m → K)
    (I : TraceFibers (fun i => commonTracePoint (y i)) →ₗ[K] W)
    (hz : ∀ i, commonTracePoint (y i) (Fin.last (m + 1)) = 1)
    (v u : Fin p → K) (a : Fin 1 → K) : AmbientEuler K m d →ₗ[K] W :=
  E + I.comp (lineFiberEvaluation (fun i => commonTracePoint (y i))
    (fun i => twoNormalVelocity (m := m) (u i) (v i)) hz (d + 1 + 1) a)

/-- The first-order remainder contributes only to the moving trace group. -/
def markedMovingRemainder (y : Fin p → Fin m → K)
    (I : TraceFibers (fun i => commonTracePoint (y i)) →ₗ[K] W)
    (hz : ∀ i, commonTracePoint (y i) (Fin.last (m + 1)) = 1)
    (d : ℕ) (v u : Fin p → K) (a : Fin 1 → K) : AmbientEuler K m d →ₗ[K] W :=
  I.comp (lineFiberRemainder (fun i => commonTracePoint (y i))
    (fun i => twoNormalVelocity (m := m) (u i) (v i)) hz (d + 1 + 1) a)

local instance markedKernelGroup (E : AmbientEuler K m d →ₗ[K] W)
    (y : Fin p → Fin m → K)
    (I : TraceFibers (fun i => commonTracePoint (y i)) →ₗ[K] W) :
    AddCommGroup (markedBaseEvaluation E y I).ker := Module.addCommMonoidToAddCommGroup K

/-- Two spanning first-response families and independent normal coordinate
classes give a maximal-rank motion of the actual marked trace. -/
theorem exists_maximal_marked_motion_of_response
    (E : AmbientEuler K m d →ₗ[K] W)
    (y : Fin p → Fin m → K)
    (I : TraceFibers (fun i => commonTracePoint (y i)) →ₗ[K] W)
    (hz : ∀ i, commonTracePoint (y i) (Fin.last (m + 1)) = 1)
    (e : (W ⧸ (markedBaseEvaluation E y I).range) ≃ₗ[K] (QA × QB))
    (α β : Fin p → Module.Dual K (markedBaseEvaluation E y I).ker)
    (hS : Submodule.span K (Set.range α) = ⊤)
    (hT : Submodule.span K (Set.range β) = ⊤)
    (hDval : ∀ (v u : Fin p → K) (F : (markedBaseEvaluation E y I).ker),
      lineFiberRemainder (fun i => commonTracePoint (y i))
        (fun i => twoNormalVelocity (m := m) (u i) (v i))
        hz (d + 1 + 1) 0 F.val =
      normalTraceFiberValues y (fun i => v i * α i F, fun i => u i * β i F))
    (cA : Fin p → QA) (cB : Fin p → QB)
    (hcA : ∀ (r : ℕ) (f : Fin r ↪ Fin p), r ≤ finrank K QA →
      LinearIndependent K (cA ∘ f))
    (hcB : ∀ (r : ℕ) (f : Fin r ↪ Fin p), r ≤ finrank K QB →
      LinearIndependent K (cB ∘ f))
    (hA : ∀ i : Fin p, e ((markedBaseEvaluation E y I).range.mkQ
      (I (normalTraceFiberValues y (Pi.single i 1, 0)))) = (cA i, 0))
    (hB : ∀ i : Fin p, e ((markedBaseEvaluation E y I).range.mkQ
      (I (normalTraceFiberValues y (0, Pi.single i 1)))) = (0, cB i)) :
    ∃ (v u : Fin p → K), (∀ i, v i = 0 ∨ v i = 1) ∧ (∀ i, u i = 0 ∨ u i = 1) ∧
      ∃ P : MvPolynomial (Fin 1) K, eval 0 P ≠ 0 ∧
        ∀ a : Fin 1 → K, a 0 ≠ 0 → eval a P ≠ 0 →
          HasMaximalRank (markedMovingEvaluation E y I hz v u a) := by
  let z := fun i => commonTracePoint (y i)
  let A₀ := markedBaseEvaluation E y I
  let A := markedMovingEvaluation E y I hz
  let D := markedMovingRemainder y I hz d
  have hpolyA (v u : Fin p → K) : IsPolynomialFamily (A v u) := by
    apply isPolynomialFamily_linearMap
    intro F
    let speed := fun i => twoNormalVelocity (m := m) (u i) (v i)
    exact (isPolynomialFamily_const (E F)).add
      (((lineFiberEvaluation_polynomial z speed hz (d + 1 + 1)).linear_comp
        (LinearMap.applyₗ F)).linear_comp I)
  have hpolyD (v u : Fin p → K) : IsPolynomialFamily (D v u) := by
    apply isPolynomialFamily_linearMap
    intro F
    let speed := fun i => twoNormalVelocity (m := m) (u i) (v i)
    exact ((lineFiberRemainder_polynomial z speed hz (d + 1 + 1)).linear_comp
      (LinearMap.applyₗ F)).linear_comp I
  have hfactor (v u : Fin p → K) (a : Fin 1 → K) : A v u a = A₀ + a 0 • D v u a := by
    apply LinearMap.ext
    intro F
    let speed := fun i => twoNormalVelocity (m := m) (u i) (v i)
    change E F + I (lineFiberEvaluation z speed hz (d + 1 + 1) a F) =
      (E F + I (traceFiberEvaluation z (d + 1 + 1) F)) +
        a 0 • I (lineFiberRemainder z speed hz (d + 1 + 1) a F)
    rw [LinearMap.congr_fun (lineFiberEvaluation_expansion z speed hz (d + 1 + 1) a) F,
      LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
    exact (add_assoc (E F) (I (traceFiberEvaluation z (d + 1 + 1) F))
      (a 0 • I (lineFiberRemainder z speed hz (d + 1 + 1) a F))).symm
  have hresponse (v u : Fin p → K) : e.toLinearMap.comp
      (DeformationGeneral.response A₀ (D v u 0) A₀.range.mkQ) =
      (firstResponse α (fun i => v i • cA i)).prod
        (firstResponse β (fun i => u i • cB i)) := by
    apply LinearMap.ext
    intro F
    let s := fun i => v i * α i F
    let t := fun i => u i * β i F
    have hDF : D v u 0 F.val = I (normalTraceFiberValues y (s, t)) :=
      congrArg I (hDval v u F)
    let π : TraceFibers z →ₗ[K] (QA × QB) :=
      e.toLinearMap.comp (A₀.range.mkQ.comp I)
    have hunitA (i : Fin p) : π (normalTraceFiberValues y (Pi.single i 1, 0)) = (cA i, 0) := hA i
    have hunitB (i : Fin p) : π (normalTraceFiberValues y (0, Pi.single i 1)) = (0, cB i) := hB i
    change e (A₀.range.mkQ (D v u 0 F.val)) = _
    rw [hDF]
    change π (normalTraceFiberValues y (s, t)) = _
    rw [normalTraceFiberValues_eq_sum, map_add, map_sum, map_sum]
    simp only [map_smul, hunitA, hunitB]
    apply Prod.ext
    · simp [Prod.fst_sum, firstResponse_apply, s, smul_smul, mul_comm]
      rfl
    · simp [Prod.snd_sum, firstResponse_apply, t, smul_smul, mul_comm]
      rfl
  exact exists_binary_two_normal_maximal_motion A₀ A D hpolyA hpolyD hfactor
    e α β cA cB hS hT hcA hcB hresponse

/-- The genuine marked motion has maximal rank once its two slice codes and
its residual kernel have the geometric identifications of Proposition 4.5. -/
theorem exists_maximal_marked_motion
    (E : AmbientEuler K m d →ₗ[K] W)
    (y : Fin p → Fin m → K)
    (I : TraceFibers (fun i => commonTracePoint (y i)) →ₗ[K] W)
    (hz : ∀ i, commonTracePoint (y i) (Fin.last (m + 1)) = 1)
    (e : (W ⧸ (markedBaseEvaluation E y I).range) ≃ₗ[K] (QA × QB))
    (w : (markedBaseEvaluation E y I).ker →ₗ[K] NormalCoefficients K m d)
    (hw : ∀ F, residualEuler K m d (w F) = F.val)
    (hS : Submodule.span K (Set.range (fun i : Fin p => (normalSCoefficient (y i)).comp w)) = ⊤)
    (hT : Submodule.span K (Set.range (fun i : Fin p => (normalTCoefficient (y i)).comp w)) = ⊤)
    (cA : Fin p → QA) (cB : Fin p → QB)
    (hcA : ∀ (r : ℕ) (f : Fin r ↪ Fin p), r ≤ finrank K QA →
      LinearIndependent K (cA ∘ f))
    (hcB : ∀ (r : ℕ) (f : Fin r ↪ Fin p), r ≤ finrank K QB →
      LinearIndependent K (cB ∘ f))
    (hA : ∀ i : Fin p, e ((markedBaseEvaluation E y I).range.mkQ
      (I (normalTraceFiberValues y (Pi.single i 1, 0)))) = (cA i, 0))
    (hB : ∀ i : Fin p, e ((markedBaseEvaluation E y I).range.mkQ
      (I (normalTraceFiberValues y (0, Pi.single i 1)))) = (0, cB i)) :
    ∃ (v u : Fin p → K), (∀ i, v i = 0 ∨ v i = 1) ∧ (∀ i, u i = 0 ∨ u i = 1) ∧
      ∃ P : MvPolynomial (Fin 1) K, eval 0 P ≠ 0 ∧
        ∀ a : Fin 1 → K, a 0 ≠ 0 → eval a P ≠ 0 →
          HasMaximalRank (markedMovingEvaluation E y I hz v u a) := by
  let α : Fin p → Module.Dual K (markedBaseEvaluation E y I).ker :=
    fun i => (normalSCoefficient (y i)).comp w
  let β : Fin p → Module.Dual K (markedBaseEvaluation E y I).ker :=
    fun i => (normalTCoefficient (y i)).comp w
  apply exists_maximal_marked_motion_of_response E y I hz e α β hS hT _ cA cB hcA hcB hA hB
  intro v u F
  rw [← hw F]
  exact lineFiberRemainder_residualEuler y u v hz (w F)

end Marked
end IdealGeneration.TwoNormalIntegral
