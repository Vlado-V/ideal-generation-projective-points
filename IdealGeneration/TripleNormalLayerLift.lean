module

public import IdealGeneration.NormalCoefficientRecovery
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The four independent layer systems in the three-normal quadratic lift. -/

noncomputable section
namespace IdealGeneration.TripleNormal.Layer

open MvPolynomial NormalDegree Matrix
open scoped Matrix

variable {K : Type*} [Field K] {h : ℕ}

abbrev Normals (K : Type*) := Fin 4 → Fin 3 → Fin 3 → K
abbrev Heights (K : Type*) := Fin 4 → Fin 3 → K
abbrev Supports (K : Type*) (h : ℕ) := Fin 4 → Fin 3 → Fin h → K
abbrev LiftInput (K : Type*) [Field K] (h : ℕ) := Forms K 3 2 × (Fin h → Fin 3 → K)

/-- The matrix of the three cone normals in layer `j`. -/
def normalMatrix (n : Normals K) (j : Fin 4) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of (n j)

/-- The base coordinate parts of the three lifted trace points are zero,
the sum of the first three unit vectors, and the sum of the next three. -/
def baseSupport (K : Type*) [Field K] (h : ℕ) : Supports K h :=
  fun _ ν i => if (ν.val = 1 ∧ i.val < 3) ∨ (ν.val = 2 ∧ 3 ≤ i.val ∧ i.val < 6)
    then 1 else 0

theorem baseSupport_eq_zero (j : Fin 4) (ν : Fin 3) (i : Fin h) (hi : 6 ≤ i.val) :
    baseSupport K h j ν i = 0 := by
  unfold baseSupport
  split_ifs with H
  · rcases H with H | H <;> omega
  · rfl

/-- The required normal evaluation of the correction in layer `j`. -/
def rhs (n : Normals K) (ζ : Heights K) (x : Supports K h) (j : Fin 4) :
    LiftInput K h →ₗ[K] (Fin 3 → K) where
  toFun f ν := -(eval (n j ν) f.1.val + ∑ i, x j ν i * (n j ν ⬝ᵥ f.2 i)) / ζ j ν
  map_add' f g := by
    funext ν
    simp [dotProduct_add, mul_add, Finset.sum_add_distrib, add_div]
    ring
  map_smul' r f := by
    funext ν
    simp [dotProduct_smul, ← Finset.mul_sum, mul_left_comm]
    ring

/-- Solve the three layer equations separately by inverting their normal matrices. -/
def correction (n : Normals K) (ζ : Heights K) (x : Supports K h) :
    LiftInput K h →ₗ[K] (Fin 4 → Fin 3 → K) :=
  LinearMap.pi fun j => ((normalMatrix n j)⁻¹).mulVecLin.comp (rhs n ζ x j)

theorem normalMatrix_correction (n : Normals K) (ζ : Heights K) (x : Supports K h)
    (j : Fin 4) (hdet : (normalMatrix n j).det ≠ 0) (f : LiftInput K h) :
    (normalMatrix n j).mulVec (correction n ζ x f j) = rhs n ζ x j f := by
  change (normalMatrix n j).mulVec ((normalMatrix n j)⁻¹.mulVec (rhs n ζ x j f)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- A change of base coordinates preserving the three layer right-hand sides
preserves the correction. -/
theorem correction_congr {h' : ℕ} (n : Normals K) (ζ : Heights K)
    (x : Supports K h) (x' : Supports K h') (Q : Forms K 3 2)
    (A : Fin h → Fin 3 → K) (A' : Fin h' → Fin 3 → K)
    (hs : ∀ j ν, ∑ i, x j ν i * (n j ν ⬝ᵥ A i) = ∑ i, x' j ν i * (n j ν ⬝ᵥ A' i)) :
    correction n ζ x (Q, A) = correction n ζ x' (Q, A') := by
  funext j
  change (normalMatrix n j)⁻¹.mulVec (rhs n ζ x j (Q, A)) =
    (normalMatrix n j)⁻¹.mulVec (rhs n ζ x' j (Q, A'))
  congr 1
  funext ν
  simp [rhs, hs j ν]

/-- Inserting further base coordinates leaves the layer coefficients unchanged
as long as the original base coefficients are preserved. -/
theorem correction_baseSupport_castAdd {e : ℕ} (n : Normals K) (ζ : Heights K)
    (hh : 6 ≤ h) (Q : Forms K 3 2) (A : Fin h → Fin 3 → K) (A' : Fin (h + e) → Fin 3 → K)
    (hA : ∀ i : Fin h, A' (i.castAdd e) = A i) :
    correction n ζ (baseSupport K h) (Q, A) =
      correction n ζ (baseSupport K (h + e)) (Q, A') := by
  apply correction_congr
  intro j ν
  rw [Fin.sum_univ_add]
  have hz : ∑ i : Fin e, baseSupport K (h + e) j ν (i.natAdd h) *
      (n j ν ⬝ᵥ A' (i.natAdd h)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [baseSupport_eq_zero j ν (i.natAdd h) (by simpa using hh.trans (Nat.le_add_right h i.val)),
      zero_mul]
  rw [hz, add_zero]
  simp [baseSupport, hA]

/-- The mixed terms supported after the first six coordinates do not need
layer corrections when the pure normal term is zero. -/
theorem correction_eq_zero_of_support (n : Normals K) (ζ : Heights K) (x : Supports K h)
    (A : Fin h → Fin 3 → K) (hx : ∀ j ν i, 6 ≤ i.val → x j ν i = 0)
    (hA : ∀ i, i.val < 6 → A i = 0) : correction n ζ x (0, A) = 0 := by
  funext j
  have hz : rhs n ζ x j (0, A) = 0 := by
    funext ν
    have hs : ∑ i, x j ν i * (n j ν ⬝ᵥ A i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i.val < 6
      · simp [hA i hi]
      · simp [hx j ν i (by omega)]
    simp [rhs, hs]
  change (normalMatrix n j)⁻¹.mulVec (rhs n ζ x j (0, A)) = 0
  rw [hz, Matrix.mulVec_zero]

/-- The normal linear form with the given three coefficients. -/
def normalForm : (Fin 3 → K) →ₗ[K] Forms K 3 1 where
  toFun a := ⟨∑ u, C (a u) * X u,
    IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _⟩
  map_add' a b := by
    apply Subtype.ext
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    apply Subtype.ext
    simp [Algebra.smul_def, Finset.mul_sum, mul_assoc]

@[simp] theorem eval_normalForm (n a : Fin 3 → K) : eval n (normalForm a).val = n ⬝ᵥ a := by
  simp [normalForm, dotProduct, mul_comm]

/-- Combine the pure normal quadratic and the base and layer mixed terms. -/
def quadratic (n : Normals K) (ζ : Heights K) (x : Supports K h) :
    LiftInput K h →ₗ[K] Forms K (3 + (h + 4)) 2 :=
  (pureExtendForm K 3 (h + 4) 2).comp (LinearMap.fst K _ _) +
    (traceLinearProduct K 3 (h + 4) 1).comp
      (LinearMap.pi fun i => Fin.addCases
        (fun b => normalForm.comp ((LinearMap.proj b).comp (LinearMap.snd K _ _)))
        (fun j => normalForm.comp ((LinearMap.proj j).comp (correction n ζ x))) i)

/-- An ambient point in normal, base, and layer coordinate order. -/
def point (n : Fin 3 → K) (x : Fin h → K) (z : Fin 4 → K) : Fin (3 + (h + 4)) → K :=
  Fin.addCases n (Fin.addCases x z)

/-- Evaluation separates the pure term and the mixed base and layer sums. -/
theorem eval_quadratic (n : Normals K) (ζ : Heights K) (x : Supports K h)
    (Q : Forms K 3 2) (A : Fin h → Fin 3 → K)
    (a : Fin 3 → K) (y : Fin h → K) (z : Fin 4 → K) :
    eval (point a y z) (quadratic n ζ x (Q, A)).val =
      eval a Q.val + (∑ i, y i * (a ⬝ᵥ A i)) +
        ∑ j, z j * (a ⬝ᵥ correction n ζ x (Q, A) j) := by
  simp only [quadratic, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    Submodule.coe_add, map_add, traceLinearProduct_val, map_sum, map_mul, eval_X]
  have ha : point a y z ∘ Fin.castAdd (h + 4) = a := by
    funext i
    simp [point]
  simp only [pureExtendForm, pureExtend, LinearMap.coe_mk, AddHom.coe_mk, eval_rename,
    point, Fin.addCases_right]
  rw [ha, Fin.sum_univ_add]
  simp [add_assoc]

/-- At a base coordinate point, the only mixed term is its base coefficient. -/
theorem eval_quadratic_base (n : Normals K) (ζ : Heights K) (x : Supports K h)
    (Q : Forms K 3 2) (A : Fin h → Fin 3 → K) (a : Fin 3 → K) (i : Fin h) :
    eval (point a (Pi.single i 1) 0) (quadratic n ζ x (Q, A)).val = eval a Q.val + a ⬝ᵥ A i := by
  rw [eval_quadratic]
  have he : ∑ b, (Pi.single i 1 : Fin h → K) b * (a ⬝ᵥ A b) = a ⬝ᵥ A i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [Pi.single_eq_of_ne hbi]
    · simp
  simp [he]

/-- The quadratic vanishes at all twelve prescribed layer cone points. -/
theorem eval_quadratic_layer (n : Normals K) (ζ : Heights K) (x : Supports K h)
    (Q : Forms K 3 2) (A : Fin h → Fin 3 → K)
    (j : Fin 4) (ν : Fin 3) (hdet : (normalMatrix n j).det ≠ 0) (hζ : ζ j ν ≠ 0) :
    eval (point (n j ν) (x j ν) (Pi.single j (ζ j ν))) (quadratic n ζ x (Q, A)).val = 0 := by
  rw [eval_quadratic, Finset.sum_eq_single j]
  · have heq := congrFun (normalMatrix_correction n ζ x j hdet (Q, A)) ν
    change n j ν ⬝ᵥ correction n ζ x (Q, A) j =
      -(eval (n j ν) Q.val + ∑ i, x j ν i * (n j ν ⬝ᵥ A i)) / ζ j ν at heq
    rw [Pi.single_eq_same, heq, mul_comm (ζ j ν), div_mul_cancel₀ _ hζ, add_neg_cancel]
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

/-- The correction never changes the prescribed pure normal quadratic. -/
theorem pureRestrict_quadratic (n : Normals K) (ζ : Heights K) (x : Supports K h)
    (Q : Forms K 3 2) (A : Fin h → Fin 3 → K) :
    pureRestrictForm K 3 (h + 4) 2 (quadratic n ζ x (Q, A)) = Q := by
  apply Subtype.ext
  simp [quadratic, pureRestrictForm, pureExtendForm, map_sum, map_mul]

/-- The lift belongs to the normal ideal, independently of its values at cone points. -/
theorem coneRestrict_quadratic (n : Normals K) (ζ : Heights K) (x : Supports K h)
    (Q : Forms K 3 2) (A : Fin h → Fin 3 → K) :
    coneRestrictForm K 3 (h + 4) 2 (quadratic n ζ x (Q, A)) = 0 := by
  have he : (coneRestrict K 3 (h + 4)).comp (pureExtend K 3 (h + 4)) =
      aeval (0 : Fin 3 → Poly K (h + 4)) := by
    ext i
    simp
  have hQ : coneRestrict K 3 (h + 4) (pureExtend K 3 (h + 4) Q.val) = 0 := by
    change ((coneRestrict K 3 (h + 4)).comp (pureExtend K 3 (h + 4))) Q.val = 0
    rw [he, aeval_zero, constantCoeff_eq, Q.property.coeff_eq_zero (by simp), map_zero]
  apply Subtype.ext
  simp [quadratic, coneRestrictForm, pureExtendForm, map_sum, map_mul, hQ]
  apply Finset.sum_eq_zero
  intro i _
  refine Fin.addCases (fun b => ?_) (fun j => ?_) i <;> simp [normalForm, map_sum, map_mul]

/-- If the base equations hold and these are all the cone points, the lift is
an actual residual quadric of the marked cone configuration. -/
theorem quadratic_mem_residual {p q : ℕ} (C : ConeConfiguration K 3 (h + 4) p q)
    (n : Normals K) (ζ : Heights K) (x : Supports K h) (a : Fin h → Fin 2 → Fin 3 → K)
    (Q : Forms K 3 2) (A : Fin h → Fin 3 → K)
    (hpoints : ∀ k, (∃ i μ, C.point k = point (a i μ) (Pi.single i 1) 0) ∨
      ∃ j ν, C.point k = point (n j ν) (x j ν) (Pi.single j (ζ j ν)))
    (hbase : ∀ i μ, eval (a i μ) Q.val + a i μ ⬝ᵥ A i = 0)
    (hdet : ∀ j, (normalMatrix n j).det ≠ 0) (hζ : ∀ j ν, ζ j ν ≠ 0) :
    quadratic n ζ x (Q, A) ∈ C.residualPiece 2 := by
  refine ⟨(C.mem_conePiece _).mpr ?_, coneRestrict_quadratic n ζ x Q A⟩
  intro k
  rcases hpoints k with ⟨i, μ, hk⟩ | ⟨j, ν, hk⟩
  · rw [hk, eval_quadratic_base, hbase]
  · rw [hk, eval_quadratic_layer n ζ x Q A j ν (hdet j) (hζ j ν)]

end IdealGeneration.TripleNormal.Layer
