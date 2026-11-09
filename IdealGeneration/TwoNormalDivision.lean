module

public import IdealGeneration.TwoNormalTrace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Homogeneous division by the two transverse normal variables. -/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial Module
set_option maxHeartbeats 800000

variable (K : Type*) [Field K] (m : ℕ)

/-- Swap the two normals on homogeneous forms. -/
def swapForm (d : ℕ) : Forms K (m + 2) d →ₗ[K] Forms K (m + 2) d where
  toFun f := ⟨swapNormals K m f.val, swapNormals_homogeneous K m f.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- Homogeneous division by the second normal variable. -/
theorem restrictA_eq_zero_iff {d : ℕ} (f : Forms K (m + 2) (d + 1)) :
    restrictA K m f.val = 0 ↔
      ∃ g : Forms K (m + 2) d, f.val = X (0 : Fin (m + 1)).succ * g.val := by
  constructor
  · intro hf
    have hswap : restrictForm K (m + 1) (d + 1) (swapForm K m (d + 1) f) = 0 :=
      Subtype.ext hf
    obtain ⟨g, hg⟩ := (restrictForm_eq_zero_iff K (m + 1)
      (swapForm K m (d + 1) f)).mp hswap
    refine ⟨swapForm K m d g, ?_⟩
    have h := congrArg (swapNormals K m) hg
    change swapNormals K m (swapNormals K m f.val) =
      swapNormals K m (X 0 * g.val) at h
    change f.val = X (0 : Fin (m + 1)).succ * swapNormals K m g.val
    simpa only [swapNormals_twice, map_mul, swapNormals_s] using h
  · rintro ⟨g, hg⟩
    rw [hg, map_mul, restrictA_t, zero_mul]

/-- A form zero on both slices has one factor of each normal variable. -/
theorem exists_double_normal_factor {d : ℕ} (f : Forms K (m + 2) (d + 1 + 1))
    (hA : restrictA K m f.val = 0)
    (hB : hyperplaneRestrict K (m + 1) f.val = 0) :
    ∃ a : Forms K (m + 2) d,
      f.val = X 0 * (X (0 : Fin (m + 1)).succ * a.val) := by
  obtain ⟨b, hb⟩ := (restrictForm_eq_zero_iff K (m + 1) f).mp (Subtype.ext hB)
  have hbA : restrictA K m b.val = 0 := by
    rw [hb, map_mul, restrictA_s] at hA
    exact (mul_eq_zero.mp hA).resolve_left (X_ne_zero 0)
  obtain ⟨a, ha⟩ := (restrictA_eq_zero_iff K m b).mp hbA
  exact ⟨a, by rw [hb, ha]⟩

end IdealGeneration.TwoNormalTrace
