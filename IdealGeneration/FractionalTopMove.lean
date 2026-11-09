module

public import IdealGeneration.DifferentialSurjectivity
public import IdealGeneration.FractionalCompatibility
public import IdealGeneration.FixedPointEulerWitness
public import IdealGeneration.CriticalOpen
public import IdealGeneration.HyperplanePoints

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The final moving point in the fractional hyperplane transfer

The resulting objects are actual ordered point configurations in the standard
projective chart.  Scalar interpolation is retained along the final motion.
-/

noncomputable section
namespace IdealGeneration.FractionalTopMove
open MvPolynomial Module HyperplaneEuler DifferentialPoint FractionalCompatibility
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {K : Type*} [Field K]

local instance relationGroup {m e : ℕ} : AddCommGroup (Relations K m e) :=
  Module.addCommMonoidToAddCommGroup K

/-- The allowed trace space cut out by the fixed trace points. -/
abbrev TraceKernel {n a : ℕ} (A : PointCoordinates K n a) (e : ℕ) :=
  (eulerTraceEvaluation A e).ker

local instance traceKernelGroup {n a e : ℕ} (A : PointCoordinates K n a) :
    AddCommGroup (TraceKernel A e) := Module.addCommMonoidToAddCommGroup K

/-- The full point configuration obtained by moving the last trace point normally. -/
def finalConfiguration {n z a : ℕ} (Z : PointCoordinates K (n + 1) z)
    (A : PointCoordinates K n a) (y : Fin n → K) (t : K) :
    PointCoordinates K (n + 1) (z + (a + 1)) :=
  appendCoordinates Z (snocPoints (embedHyperplanePoints A) (Fin.cons t y))

@[simp] theorem final_chart_off {n z a : ℕ} (Z : PointCoordinates K (n + 1) z)
    (A : PointCoordinates K n a) (y : Fin n → K) (t : K) (i : Fin z) :
    chartPoint K (finalConfiguration Z A y t) (Fin.castAdd (a + 1) i) =
      chartPoint K Z i := by
  exact chartPoint_append_left Z _ i

@[simp] theorem final_chart_on {n z a : ℕ} (Z : PointCoordinates K (n + 1) z)
    (A : PointCoordinates K n a) (y : Fin n → K) (t : K) (i : Fin a) :
    chartPoint K (finalConfiguration Z A y t) (Fin.natAdd z i.castSucc) =
      Fin.cons 0 (chartPoint K A i) := by
  rw [finalConfiguration, chartPoint_append_right]
  have h : chartPoint K (snocPoints (embedHyperplanePoints A) (Fin.cons t y)) i.castSucc =
      chartPoint K (embedHyperplanePoints A) i := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [chartPoint, snocPoints]
  rw [h, chartPoint_embedHyperplanePoints]

@[simp] theorem final_chart_moving {n z a : ℕ} (Z : PointCoordinates K (n + 1) z)
    (A : PointCoordinates K n a) (y : Fin n → K) (t : K) :
    chartPoint K (finalConfiguration Z A y t) (Fin.natAdd z (Fin.last a)) =
      Fin.cons t (Fin.snoc y 1) := by
  rw [finalConfiguration, chartPoint_append_right]
  have h : chartPoint K (snocPoints (embedHyperplanePoints A) (Fin.cons t y)) (Fin.last a) =
      Fin.snoc (Fin.cons t y) 1 := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [chartPoint, snocPoints]
  rw [h]
  exact (Fin.cons_snoc_eq_snoc_cons t y 1).symm

@[simp] theorem finalConfiguration_zero {n z a : ℕ} (Z : PointCoordinates K (n + 1) z)
    (A : PointCoordinates K n a) (y : Fin n → K) :
    finalConfiguration Z A y 0 = hyperplaneConfiguration Z (snocPoints A y) := by
  have hembed : snocPoints (embedHyperplanePoints A) (Fin.cons 0 y) =
      embedHyperplanePoints (snocPoints A y) := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.lastCases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun k => ?_) j <;> simp [embedHyperplanePoints, snocPoints]
    · simp [embedHyperplanePoints, snocPoints]
  unfold finalConfiguration
  rw [hembed]
  rfl

/-- Every coordinate of the configuration depends affinely on the moving parameter. -/
theorem finalConfiguration_affine {n z a : ℕ} (Z : PointCoordinates K (n + 1) z)
    (A : PointCoordinates K n a) (y : Fin n → K) (t : K) :
    finalConfiguration Z A y t = fun ij => finalConfiguration Z A y 0 ij +
      t * (finalConfiguration Z A y 1 ij - finalConfiguration Z A y 0 ij) := by
  funext ij
  rcases ij with ⟨i, j⟩
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp only [finalConfiguration, appendCoordinates, Fin.addCases_left]
    ring
  · intro k
    simp only [finalConfiguration, appendCoordinates, Fin.addCases_right]
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp only [snocPoints, Fin.snoc_last]
      refine Fin.cases ?_ (fun l => ?_) j <;> simp
    · simp only [snocPoints, Fin.snoc_castSucc]
      ring

/-- Scalar surjectivity stays valid on a principal open of an affine configuration line. -/
theorem scalar_line_principal_open {m p e : ℕ}
    (Q V : PointCoordinates K m p)
    (hQ : Function.Surjective (pointEvaluation K Q e)) :
    ∃ S : MvPolynomial (Fin 1) K, eval 0 S ≠ 0 ∧
      ∀ t : K, eval (fun _ => t) S ≠ 0 →
        Function.Surjective (pointEvaluation K (fun ij => Q ij + t * V ij) e) := by
  obtain ⟨D, hD, hgood⟩ := pointEvaluation_surjective_principal_open Q hQ
  let S := DeformationMatrix.polynomialInOneCoordinate (DifferentialLine.lineSubstitution Q V D)
  have hS (t : K) : eval (fun _ : Fin 1 => t) S =
      eval (fun ij => Q ij + t * V ij) D := by
    rw [DeformationMatrix.eval_polynomialInOneCoordinate, DifferentialLine.eval_lineSubstitution]
  refine ⟨S, ?_, fun t ht => hgood _ (by rwa [← hS t])⟩
  have h : eval (fun _ : Fin 1 => (0 : K)) S ≠ 0 := by
    rw [hS]
    simpa using hD
  exact h

/-- The scalar postulation hypotheses in the paper persist during the final movement. -/
theorem final_scalar_principal_open {n z a d : ℕ}
    (Z : PointCoordinates K (n + 1) z) (A : PointCoordinates K n a) (y : Fin n → K)
    (hZ : ∀ i, Z (i, 0) ≠ 0)
    (hscalarZ : Function.Surjective (pointEvaluation K Z d))
    (hscalarA : Function.Surjective (pointEvaluation K (snocPoints A y) (d + 1))) :
    ∃ S : MvPolynomial (Fin 1) K, eval 0 S ≠ 0 ∧
      ∀ t : K, eval (fun _ => t) S ≠ 0 →
        Function.Surjective (pointEvaluation K (finalConfiguration Z A y t) (d + 1)) := by
  have hzero : Function.Surjective (pointEvaluation K (finalConfiguration Z A y 0) (d + 1)) := by
    rw [finalConfiguration_zero]
    exact pointEvaluation_hyperplaneConfiguration_surjective Z (snocPoints A y) hZ hscalarZ hscalarA
  obtain ⟨S, hS, hgood⟩ := scalar_line_principal_open
    (finalConfiguration Z A y 0)
    (fun ij => finalConfiguration Z A y 1 ij - finalConfiguration Z A y 0 ij) hzero
  refine ⟨S, hS, fun t ht => ?_⟩
  simpa only [← finalConfiguration_affine] using hgood t ht

/-- The trace kernel imposes all components of trace vanishing at the fixed trace points. -/
theorem traceKernel_vanishes {n a e : ℕ} (A : PointCoordinates K n a)
    (b : TraceKernel A e) (i : Fin a) :
    vectorEvaluation (chartPoint K A i) b.val = 0 := by
  have hmem : b.val ∈ (eulerTraceEvaluation A e).ker := b.property
  rw [eulerTraceEvaluation_ker_eq] at hmem
  funext j
  exact congrFun (congrFun hmem j) i

/-- Full Euler vanishing on the final configuration is precisely the fixed problem
and the value at the moving point. -/
theorem final_euler_zero_iff {n z a d : ℕ}
    (Z : PointCoordinates K (n + 1) z) (A : PointCoordinates K n a)
    (y : Fin n → K) (t : K) (f : Relations K (n + 2) (d + 1)) :
    eulerEvaluation (finalConfiguration Z A y t) (d + 1) f = 0 ↔
      f ∈ fixedSpace (chartPoint K Z) (fun i => Fin.cons 0 (chartPoint K A i))
        (TraceKernel A (d + 1)) ∧
      vectorEvaluation (Fin.cons t (Fin.snoc y 1)) f = 0 := by
  rw [eulerEvaluation_eq_zero_iff]
  constructor
  · intro hf
    have hoff (i : Fin z) : vectorEvaluation (chartPoint K Z i) f = 0 := by
      funext j
      simpa only [final_chart_off, vectorEvaluation_apply, Pi.zero_apply] using hf (Fin.castAdd (a + 1) i) j
    have hon (i : Fin a) : vectorEvaluation (Fin.cons 0 (chartPoint K A i)) f = 0 := by
      funext j
      simpa only [final_chart_on, vectorEvaluation_apply, Pi.zero_apply] using hf (Fin.natAdd z i.castSucc) j
    have htrace : trace K (n + 1) (d + 1) f ∈ TraceKernel A (d + 1) := by
      funext i j
      change vectorEvaluation (chartPoint K A i) (trace K (n + 1) (d + 1) f) j.castSucc = 0
      have ht := trace_evaluation (Fin.cons 0 (chartPoint K A i)) rfl f j.castSucc
      have ht' : vectorEvaluation (chartPoint K A i) (trace K (n + 1) (d + 1) f) j.castSucc =
          vectorEvaluation (Fin.cons 0 (chartPoint K A i)) f j.castSucc.succ := by
        simpa only [Fin.cons_succ] using ht
      rw [ht']
      exact congrFun (hon i) j.castSucc.succ
    refine ⟨⟨htrace, hoff, hon⟩, ?_⟩
    funext j
    simpa only [final_chart_moving, vectorEvaluation_apply, Pi.zero_apply] using hf (Fin.natAdd z (Fin.last a)) j
  · rintro ⟨hf, hmove⟩ i j
    refine Fin.addCases ?_ ?_ i
    · intro k
      simpa only [final_chart_off, vectorEvaluation_apply, Pi.zero_apply] using congrFun (hf.2.1 k) j
    · intro k
      refine Fin.lastCases ?_ (fun l => ?_) k
      · simpa only [final_chart_moving, vectorEvaluation_apply, Pi.zero_apply] using congrFun hmove j
      · simpa only [final_chart_on, vectorEvaluation_apply, Pi.zero_apply] using congrFun (hf.2.2 l) j

/-- Injective residual conditions give a genuine injective multiplication witness after the motion. -/
theorem exists_final_injective [Infinite K] {n z a d : ℕ}
    (Z : PointCoordinates K (n + 1) z) (A : PointCoordinates K n a) (y : Fin n → K)
    (hZ : ∀ i, Z (i, 0) ≠ 0)
    (htrace : Function.Injective
      ((vectorEvaluation (Fin.snoc y 1)).comp (TraceKernel A (d + 1)).subtype))
    (hres : Function.Injective (residualConditions (chartPoint K Z)
      (fun i => Fin.cons 0 (chartPoint K A i)) (TraceKernel A (d + 1))
      (Fin.cons 0 (Fin.snoc y 1)))) :
    ∃ t : K, t ≠ 0 ∧ Function.Injective (pointMultiplication (finalConfiguration Z A y t) (d + 1)) := by
  let y₀ : Fin (n + 2) → K := Fin.cons 0 (Fin.snoc y 1)
  let v : Fin (n + 2) → K := Fin.cons 1 0
  have hreszero : ∀ g : Fin (n + 1) → Forms K (n + 2) d,
      (∀ i j, eval (chartPoint K Z i) (g j).val = 0) →
      (∀ i, eval (Fin.cons 0 (chartPoint K A i)) (tangentProduct K (n + 1) d g).val = 0) →
      (fun i => eval y₀ (g i).val) ∈ traceImage (TraceKernel A (d + 1)) y₀ → g = 0 := by
    intro g hoff hon hvalue
    have hz : residualConditions (chartPoint K Z)
        (fun i => Fin.cons 0 (chartPoint K A i)) (TraceKernel A (d + 1)) y₀ g = 0 := by
      apply Prod.ext
      · apply Prod.ext
        · funext i j
          exact hoff i j
        · funext i
          exact hon i
      · exact (Submodule.Quotient.mk_eq_zero _).mpr hvalue
    exact hres (hz.trans (map_zero _).symm)
  obtain ⟨t, ht, _hoff, hinj⟩ := exists_moving_point_injective
    (chartPoint K Z) (fun i => Fin.cons 0 (chartPoint K A i))
    (TraceKernel A (d + 1)) y₀ v rfl (by simp [v])
    (fun i => by simpa [chartPoint] using hZ i) htrace hreszero
  have heuler : Function.Injective (eulerEvaluation (finalConfiguration Z A y t) (d + 1)) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    obtain ⟨hfixed, hmove⟩ := (final_euler_zero_iff Z A y t f).mp hf
    have hline : (fun i => y₀ i + t * v i) = Fin.cons t (Fin.snoc y 1) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [y₀, v]
    have hz : (⟨f, hfixed⟩ : fixedSpace (chartPoint K Z)
        (fun i => Fin.cons 0 (chartPoint K A i)) (TraceKernel A (d + 1))) = 0 := by
      apply hinj
      change vectorEvaluation (fun i => y₀ i + t * v i) f = 0
      rwa [hline]
    exact congrArg Subtype.val hz
  refine ⟨t, ht, ?_⟩
  exact (pointMultiplication_injective_iff _ _).mpr
    ((pointEulerSquare _ _).injective_iff.mpr
      ((eulerEvaluation_injective_iff _ _).mp heuler))

/-- The injective moving-point construction proves the general-points statement. -/
theorem idealGenerationAt_of_top_injective [CharZero K] {n z a d : ℕ}
    (Z : PointCoordinates K (n + 1) z) (A : PointCoordinates K n a) (y : Fin n → K)
    (hZ : ∀ i, Z (i, 0) ≠ 0)
    (htrace : Function.Injective
      ((vectorEvaluation (Fin.snoc y 1)).comp (TraceKernel A (d + 1)).subtype))
    (hres : Function.Injective (residualConditions (chartPoint K Z)
      (fun i => Fin.cons 0 (chartPoint K A i)) (TraceKernel A (d + 1))
      (Fin.cons 0 (Fin.snoc y 1)))) :
    IdealGenerationAt K (n + 1) (d + 1) (z + (a + 1)) := by
  obtain ⟨t, _, ht⟩ := exists_final_injective Z A y hZ htrace hres
  exact idealGenerationAt_of_injective_witness (by omega) (finalConfiguration Z A y t) ht

section KernelTransfer
variable {V W Q : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- Equal kernels and equal target dimensions transfer surjectivity. -/
theorem surjective_of_same_kernel (F : V →ₗ[K] W) (G : V →ₗ[K] Q)
    (hker : F.ker = G.ker) (hdim : finrank K W = finrank K Q)
    (hF : Function.Surjective F) : Function.Surjective G := by
  have hrank : finrank K F.range = finrank K G.range := by
    have hf := F.finrank_range_add_finrank_ker
    have hg := G.finrank_range_add_finrank_ker
    rw [hker] at hf
    omega
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [← hrank, LinearMap.range_eq_top.mpr hF, finrank_top, hdim]

end KernelTransfer

/-- The differential full-condition map and actual reduced Euler evaluation have the same kernel. -/
theorem final_condition_kernel_eq {n z a d : ℕ}
    (Z : PointCoordinates K (n + 1) z) (A : PointCoordinates K n a)
    (y : Fin n → K) (t : K) (hZ : ∀ i, Z (i, 0) ≠ 0) :
    ((fixedConditionEvaluation (chartPoint K Z)
      (fun i => Fin.cons 0 (chartPoint K A i)) (eulerTraceEvaluation A (d + 1))).prod
        (chartEvaluation (Fin.cons t (Fin.snoc y 1)))).ker =
      (eulerTraceEvaluation (finalConfiguration Z A y t) (d + 1)).ker := by
  have hoff : ∀ i, chartPoint K Z i 0 ≠ 0 := by
    intro i
    simpa [chartPoint] using hZ i
  have hTon : ∀ b : (eulerTraceEvaluation A (d + 1)).ker, ∀ i,
      vectorEvaluation (chartPoint K A i) b.val = 0 := by
    intro b i
    exact traceKernel_vanishes A b i
  have hfixed := fixedConditionEvaluation_ker (chartPoint K Z)
    (fun i => Fin.cons 0 (chartPoint K A i)) (eulerTraceEvaluation A (d + 1))
    hoff (fun _ => rfl) hTon
  ext f
  have hfixedf : fixedConditionEvaluation (chartPoint K Z)
      (fun i => Fin.cons 0 (chartPoint K A i)) (eulerTraceEvaluation A (d + 1)) f = 0 ↔
      f ∈ fixedSpace (chartPoint K Z) (fun i => Fin.cons 0 (chartPoint K A i))
        (TraceKernel A (d + 1)) := by
    change f ∈ (fixedConditionEvaluation (chartPoint K Z)
      (fun i => Fin.cons 0 (chartPoint K A i)) (eulerTraceEvaluation A (d + 1))).ker ↔ _
    rw [hfixed]
  have hreduced : eulerTraceEvaluation (finalConfiguration Z A y t) (d + 1) f = 0 ↔
      eulerEvaluation (finalConfiguration Z A y t) (d + 1) f = 0 := by
    change f ∈ (eulerTraceEvaluation (finalConfiguration Z A y t) (d + 1)).ker ↔
      f ∈ (eulerEvaluation (finalConfiguration Z A y t) (d + 1)).ker
    rw [eulerTraceEvaluation_ker_eq]
  change (_, _) = 0 ↔ eulerTraceEvaluation (finalConfiguration Z A y t) (d + 1) f = 0
  rw [Prod.mk_eq_zero, hfixedf, hreduced, final_euler_zero_iff,
    chartEvaluation_eq_zero_iff _ (by simp)]

/-- Independent differential conditions give actual surjective reduced Euler evaluation. -/
theorem final_eulerTrace_surjective_of_conditions {n z a d : ℕ}
    (Z : PointCoordinates K (n + 1) z) (A : PointCoordinates K n a)
    (y : Fin n → K) (t : K) (hZ : ∀ i, Z (i, 0) ≠ 0)
    (h : Function.Surjective ((fixedConditionEvaluation (chartPoint K Z)
      (fun i => Fin.cons 0 (chartPoint K A i)) (eulerTraceEvaluation A (d + 1))).prod
        (chartEvaluation (Fin.cons t (Fin.snoc y 1))))) :
    Function.Surjective (eulerTraceEvaluation (finalConfiguration Z A y t) (d + 1)) := by
  apply surjective_of_same_kernel _ _ (final_condition_kernel_eq Z A y t hZ) _ h
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, finrank_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  ring

/-- Surjective reduced Euler evaluation and scalar postulation imply surjective multiplication. -/
theorem multiplication_surjective_of_eulerTrace [CharZero K] {m p e : ℕ}
    (Q : PointCoordinates K m p)
    (hscalar : Function.Surjective (pointEvaluation K Q e))
    (hEuler : Function.Surjective (eulerTraceEvaluation Q e)) :
    Function.Surjective (pointMultiplication Q e) := by
  have hkernel : (eulerTraceEvaluation Q e).ker = (pointEulerSquare Q e).leftOnKernel.ker :=
    (eulerTraceEvaluation_ker_eq Q e).trans (eulerEvaluation_ker_eq Q e)
  have hdim : finrank K (Fin p → Fin m → K) = finrank K (fiberMultiplication Q).ker := by
    rw [finrank_fiberMultiplication_ker]
    simp [Module.finrank_pi_fintype, Nat.mul_comm]
  have hleft := surjective_of_same_kernel (eulerTraceEvaluation Q e)
    (pointEulerSquare Q e).leftOnKernel hkernel hdim hEuler
  apply (pointMultiplication_surjective_iff Q e).mpr
  exact ((pointEulerSquare Q e).surjective_iff (formMultiplication_surjective (m + 1) e)
    (componentEvaluation_surjective Q hscalar)).mpr hleft

/-- The surjective top movement preserves scalar postulation at the same parameter. -/
theorem exists_final_surjective [CharZero K] {n z a d : ℕ}
    (Z : PointCoordinates K (n + 1) z) (A : PointCoordinates K n a) (y : Fin n → K)
    (hZ : ∀ i, Z (i, 0) ≠ 0)
    (hT : Function.Surjective (eulerTraceEvaluation A (d + 1)))
    (hres : Function.Surjective (residualConditions (chartPoint K Z)
      (fun i => Fin.cons 0 (chartPoint K A i)) (TraceKernel A (d + 1))
      (Fin.cons 0 (Fin.snoc y 1))))
    (hscalarZ : Function.Surjective (pointEvaluation K Z d))
    (hscalarA : Function.Surjective (pointEvaluation K (snocPoints A y) (d + 1))) :
    ∃ t : K, t ≠ 0 ∧
      Function.Surjective (pointEvaluation K (finalConfiguration Z A y t) (d + 1)) ∧
      Function.Surjective (pointMultiplication (finalConfiguration Z A y t) (d + 1)) := by
  let y₀ : Fin (n + 2) → K := Fin.cons 0 (Fin.snoc y 1)
  let v : Fin (n + 2) → K := Fin.cons 1 0
  have hline (t : K) : (fun i => y₀ i + t * v i) = Fin.cons t (Fin.snoc y 1) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [y₀, v]
  have hTon : ∀ b : (eulerTraceEvaluation A (d + 1)).ker, ∀ i,
      vectorEvaluation (chartPoint K A i) b.val = 0 := by
    intro b i
    exact traceKernel_vanishes A b i
  obtain ⟨P, hP, hgoodP⟩ := moving_point_independent_principal_open
    (chartPoint K Z) (fun i => Fin.cons 0 (chartPoint K A i))
    (eulerTraceEvaluation A (d + 1)) y₀ v rfl (by simp [v]) (by simp [y₀])
    (fun i => by simpa [chartPoint] using hZ i) (fun _ => rfl) hTon hT hres
  obtain ⟨S, hS, hgoodS⟩ := final_scalar_principal_open Z A y hZ hscalarZ hscalarA
  have hPS : eval (0 : Fin 1 → K) (P * S) ≠ 0 := by simpa using mul_ne_zero hP hS
  obtain ⟨t, ht, htPS, _⟩ := DifferentialResponse.exists_parameter_avoiding_finite
    (P * S) hPS ∅ Set.finite_empty
  have hparts : eval (fun _ : Fin 1 => t) P ≠ 0 ∧ eval (fun _ : Fin 1 => t) S ≠ 0 := by
    simpa using htPS
  have hscalar := hgoodS t hparts.2
  refine ⟨t, ht, hscalar, multiplication_surjective_of_eulerTrace _ hscalar ?_⟩
  apply final_eulerTrace_surjective_of_conditions Z A y t hZ
  have h := hgoodP t ht hparts.1
  rwa [hline] at h

/-- The surjective top movement proves the general-points ideal-generation assertion. -/
theorem idealGenerationAt_of_top_surjective [CharZero K] {n z a d : ℕ}
    (Z : PointCoordinates K (n + 1) z) (A : PointCoordinates K n a) (y : Fin n → K)
    (hZ : ∀ i, Z (i, 0) ≠ 0)
    (hT : Function.Surjective (eulerTraceEvaluation A (d + 1)))
    (hres : Function.Surjective (residualConditions (chartPoint K Z)
      (fun i => Fin.cons 0 (chartPoint K A i)) (TraceKernel A (d + 1))
      (Fin.cons 0 (Fin.snoc y 1))))
    (hscalarZ : Function.Surjective (pointEvaluation K Z d))
    (hscalarA : Function.Surjective (pointEvaluation K (snocPoints A y) (d + 1))) :
    IdealGenerationAt K (n + 1) (d + 1) (z + (a + 1)) := by
  obtain ⟨t, _, hscalar, hmul⟩ := exists_final_surjective Z A y hZ hT hres hscalarZ hscalarA
  exact idealGenerationAt_of_witness (by omega) (finalConfiguration Z A y t) hscalar (Or.inr hmul)

end IdealGeneration.FractionalTopMove
