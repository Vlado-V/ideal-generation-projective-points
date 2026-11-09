module

public import IdealGeneration.CubicInitialResidueEvaluation
public import IdealGeneration.CubicInitialNormalPackedData
public import IdealGeneration.CubicInitialTracePackedData
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Recover the full evaluation kernels from the checked block products. -/

noncomputable section
namespace IdealGeneration.CubicInitial
open Matrix Module CertifiedRank

local instance kernelBridgePrime : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

private theorem split_product {K : Type*} [Field K] {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin (m + k)) K)
    (h : ∀ i j, (A * B) i j = if i.val = j.val then 1 else 0) :
    Function.Surjective A.mulVec ∧
      A * B.submatrix id (Fin.natAdd m : Fin k → Fin (m + k)) = 0 := by
  have hinv : A * B.submatrix id (Fin.castAdd k : Fin m → Fin (m + k)) = 1 := by
    ext i j
    change (A * B) i (j.castAdd k) = (1 : Matrix (Fin m) (Fin m) K) i j
    rw [h]
    simp [Matrix.one_apply, Fin.ext_iff]
  refine ⟨Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨_, hinv⟩, ?_⟩
  ext i j
  change (A * B) i (j.natAdd m) = 0
  have hne : i.val ≠ (j.natAdd m).val := by
    simp only [Fin.val_natAdd]
    omega
  rw [h, ite_eq_right hne]

/-- An independent list of the required size spans a full evaluation kernel. -/
theorem kernel_columns_span {K : Type*} [Field K] {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin k) K)
    (hcard : n = m + k) (hA : Function.Surjective A.mulVec)
    (hB : A * B = 0) (free : Fin k → Fin n)
    (hfree : B.submatrix free id = 1) :
    ∀ u, A.mulVec u = 0 → ∃ v, B.mulVec v = u := by
  let f := A.mulVecLin
  let g := B.mulVecLin
  have hi : Function.Injective g := by
    intro x y hxy
    have hfreeVec (v : Fin k → K) : (B.mulVec v) ∘ free = v := by
      have h := Matrix.submatrix_mulVec_equiv B v free (Equiv.refl (Fin k))
      change (B.submatrix free id).mulVec v = (B.mulVec v) ∘ free at h
      rw [hfree, Matrix.one_mulVec] at h
      exact h.symm
    rw [← hfreeVec x, ← hfreeVec y]
    exact congrArg (fun w => w ∘ free) hxy
  have hle : g.range ≤ f.ker := by
    rintro u ⟨v, rfl⟩
    change A.mulVec (B.mulVec v) = 0
    rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  have hd := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hA, finrank_top] at hd
  have hm : finrank K (Fin m → K) = m := by simp
  have hn : finrank K (Fin n → K) = n := by simp
  have hk : finrank K (Fin k → K) = k := by simp
  rw [hm, hn] at hd
  have heq : g.range = f.ker := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [LinearMap.finrank_range_of_inj hi, hk]
    omega
  intro u hu
  have hmem : u ∈ f.ker := hu
  rw [← heq] at hmem
  exact hmem

def normalKernel : Matrix (Fin 144) (Fin 36) (ZMod 1009) :=
  fun i j => normalKernelEntry i j

def traceKernel : Matrix (Fin 220) (Fin 55) (ZMod 1009) :=
  fun i j => traceKernelEntry i j

def normalFree (j : Fin 36) : Fin 144 := Fin.ofNat 144 normalFreeData[j.val]!
def traceFree (j : Fin 55) : Fin 220 := Fin.ofNat 220 traceFreeData[j.val]!

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem normalKernel_free : normalKernel.submatrix normalFree id = 1 := by
  have h : ∀ i j : Fin 36, normalKernelEntry (normalFree i) j = if i = j then 1 else 0 :=
    by decide +kernel
  ext i j
  change (normalKernelEntry (normalFree i) j : ZMod 1009) = _
  rw [h, Matrix.one_apply]
  split <;> simp

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem traceKernel_free : traceKernel.submatrix traceFree id = 1 := by
  have h : ∀ i j : Fin 55, traceKernelEntry (traceFree i) j = if i = j then 1 else 0 :=
    by decide +kernel
  ext i j
  change (traceKernelEntry (traceFree i) j : ZMod 1009) = _
  rw [h, Matrix.one_apply]
  split <;> simp

theorem normalEvaluation_kernel_of_factorization
    (h : normalResidueEvaluation.map (Nat.castRingHom (ZMod 1009)) *
        normalFactor.map (Nat.castRingHom (ZMod 1009)) =
      Matrix.map normalIdentityBlock (Nat.castRingHom (ZMod 1009))) :
    Function.Surjective (normalEvaluationMatrix (ZMod 1009)).mulVec ∧
      ∀ u, (normalEvaluationMatrix (ZMod 1009)).mulVec u = 0 →
        ∃ v, normalKernel.mulVec v = u := by
  rw [normalResidueEvaluation_map] at h
  have h' (i : Fin 108) (j : Fin (108 + 36)) :
      (normalEvaluationMatrix (ZMod 1009) *
        normalFactor.map (Nat.castRingHom (ZMod 1009))) i j =
        if i.val = j.val then 1 else 0 := by
    rw [h]
    change (normalIdentityBlock i j : ZMod 1009) = _
    simp [normalIdentityBlock, apply_ite]
  obtain ⟨hs, hz⟩ := split_product _ _ h'
  have hk : normalEvaluationMatrix (ZMod 1009) * normalKernel = 0 := by
    have he : (normalFactor.map (Nat.castRingHom (ZMod 1009))).submatrix id
        (Fin.natAdd 108) = normalKernel := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.map_apply, id_eq, normalFactor,
        Fin.addCases_right, normalKernel]
      rfl
    rw [he] at hz
    exact hz
  exact ⟨hs, kernel_columns_span _ _ rfl hs hk normalFree normalKernel_free⟩

theorem traceEvaluation_kernel_of_factorization
    (h : traceResidueEvaluation.map (Nat.castRingHom (ZMod 1009)) *
        traceFactor.map (Nat.castRingHom (ZMod 1009)) =
      Matrix.map traceIdentityBlock (Nat.castRingHom (ZMod 1009))) :
    Function.Surjective (traceEvaluationMatrix (ZMod 1009)).mulVec ∧
      ∀ u, (traceEvaluationMatrix (ZMod 1009)).mulVec u = 0 →
        ∃ v, traceKernel.mulVec v = u := by
  rw [traceResidueEvaluation_map] at h
  have h' (i : Fin 165) (j : Fin (165 + 55)) :
      (traceEvaluationMatrix (ZMod 1009) *
        traceFactor.map (Nat.castRingHom (ZMod 1009))) i j =
        if i.val = j.val then 1 else 0 := by
    rw [h]
    change (traceIdentityBlock i j : ZMod 1009) = _
    simp [traceIdentityBlock, apply_ite]
  obtain ⟨hs, hz⟩ := split_product _ _ h'
  have hk : traceEvaluationMatrix (ZMod 1009) * traceKernel = 0 := by
    have he : (traceFactor.map (Nat.castRingHom (ZMod 1009))).submatrix id
        (Fin.natAdd 165) = traceKernel := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.map_apply, id_eq, traceFactor,
        Fin.addCases_right, traceKernel]
      rfl
    rw [he] at hz
    exact hz
  exact ⟨hs, kernel_columns_span _ _ rfl hs hk traceFree traceKernel_free⟩

end IdealGeneration.CubicInitial
