module

public import IdealGeneration.TripleNormalConic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The leading plane and root blocks in the ordered three-normal interpolation. -/

namespace IdealGeneration.TripleNormal

open Matrix
open scoped Matrix

abbrev GroupedLeadingRow (G : ℕ) := (Fin G × Fin 2 × Fin 3) ⊕ (Fin 9 × Fin 3)
abbrev GroupedLeadingCol (G : ℕ) := (Fin G × Fin 3 × Fin 2) ⊕ (Fin 9 × Fin 3)

variable {K : Type*} [Field K] {G : ℕ}

/-- Each plane row sees the two incident edges, and each root sees only its own columns. -/
def groupedLeadingMatrix (P : Fin G → Fin 3 → Fin 2 → Fin 3 → K)
    (R : Fin 9 → Fin 3 → Fin 3 → K) : Matrix (GroupedLeadingRow G) (GroupedLeadingCol G) K :=
  Matrix.fromBlocks
    (Matrix.of fun (g, p, i) (g', e, j) =>
      if g' = g then if e = p.castSucc ∨ e = p.succ then P g e j i else 0 else 0)
    0 0 (Matrix.of fun (r, i) (r', j) => if r' = r then R r j i else 0)

/-- A plane row returns the sum of the two incident edge vectors. -/
theorem groupedLeadingMatrix_mulVec_plane (P : Fin G → Fin 3 → Fin 2 → Fin 3 → K)
    (R : Fin 9 → Fin 3 → Fin 3 → K) (x : GroupedLeadingCol G → K) (g : Fin G)
    (p : Fin 2) (i : Fin 3) :
    (groupedLeadingMatrix P R).mulVec x (.inl (g, p, i)) =
      (∑ j, x (.inl (g, p.castSucc, j)) • P g p.castSucc j) i +
        (∑ j, x (.inl (g, p.succ, j)) • P g p.succ j) i := by
  rw [groupedLeadingMatrix, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, Sum.elim_inl, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Function.comp_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single g]
  · fin_cases p <;> simp [Fin.sum_univ_three, Finset.sum_apply, mul_comm]
  · intro g' _ hne
    simp [hne]
  · simp

/-- A root row returns the corresponding linear combination of its three local columns. -/
theorem groupedLeadingMatrix_mulVec_root (P : Fin G → Fin 3 → Fin 2 → Fin 3 → K)
    (R : Fin 9 → Fin 3 → Fin 3 → K) (x : GroupedLeadingCol G → K) (r : Fin 9) (i : Fin 3) :
    (groupedLeadingMatrix P R).mulVec x (.inr (r, i)) =
      (∑ j, x (.inr (r, j)) • R r j) i := by
  rw [groupedLeadingMatrix, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, zero_add, Sum.elim_inr, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Function.comp_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single r]
  · simp [Finset.sum_apply, mul_comm]
  · intro r' _ hne
    simp [hne]
  · simp

/-- Independent chord normals and independent local column vectors give an injective matrix. -/
theorem groupedLeadingMatrix_mulVec_injective (P : Fin G → Fin 3 → Fin 2 → Fin 3 → K)
    (R : Fin 9 → Fin 3 → Fin 3 → K) (n : Fin G → Fin 3 → Fin 3 → K)
    (horth : ∀ g e j, n g e ⬝ᵥ P g e j = 0) (hn : ∀ g, (Matrix.of (n g)).det ≠ 0)
    (hP : ∀ g e, LinearIndependent K (P g e)) (hR : ∀ r, LinearIndependent K (R r)) :
    Function.Injective (groupedLeadingMatrix P R).mulVec := by
  have hker (x : GroupedLeadingCol G → K) (hx : (groupedLeadingMatrix P R).mulVec x = 0) : x = 0 := by
    let A (g : Fin G) (e : Fin 3) : Fin 3 → K := ∑ j, x (.inl (g, e, j)) • P g e j
    have hA (g : Fin G) (e : Fin 3) : n g e ⬝ᵥ A g e = 0 := by
      simp [A, dotProduct_smul, horth]
    have hplane (g : Fin G) (p : Fin 2) : A g p.castSucc + A g p.succ = 0 := by
      funext i
      exact (groupedLeadingMatrix_mulVec_plane P R x g p i).symm.trans (congrFun hx (.inl (g, p, i)))
    have hAz (g : Fin G) (e : Fin 3) : A g e = 0 := by
      have hrows : Matrix.of ![n g 0, n g 1, n g 2] = Matrix.of (n g) := by
        ext i j
        fin_cases i <;> rfl
      have h := chordPlane_leadingBlock_kernel (n g 0) (n g 1) (n g 2) (A g 0) (A g 1) (A g 2)
        (by rw [hrows]; exact hn g) (hA g 0) (hA g 1) (hA g 2) (hplane g 0) (hplane g 1)
      fin_cases e
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    funext c
    rcases c with ⟨g, e, j⟩ | ⟨r, j⟩
    · exact (Fintype.linearIndependent_iff.mp (hP g e)) _ (hAz g e) j
    · apply (Fintype.linearIndependent_iff.mp (hR r)) (fun j => x (.inr (r, j))) _ j
      funext i
      exact (groupedLeadingMatrix_mulVec_root P R x r i).symm.trans (congrFun hx (.inr (r, i)))
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker
  rw [Matrix.mulVec_sub, hxy, sub_self]

/-- Putting the leading rows and columns in a common order gives a nonzero determinant. -/
theorem groupedLeadingMatrix_reindex_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Fin G → Fin 3 → Fin 2 → Fin 3 → K) (R : Fin 9 → Fin 3 → Fin 3 → K)
    (n : Fin G → Fin 3 → Fin 3 → K)
    (horth : ∀ g e j, n g e ⬝ᵥ P g e j = 0) (hn : ∀ g, (Matrix.of (n g)).det ≠ 0)
    (hP : ∀ g e, LinearIndependent K (P g e)) (hR : ∀ r, LinearIndependent K (R r))
    (er : ι ≃ GroupedLeadingRow G) (ec : ι ≃ GroupedLeadingCol G) :
    ((groupedLeadingMatrix P R).submatrix er ec).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  simp only [Matrix.submatrix_mulVec_equiv] at hxy
  have hm : (groupedLeadingMatrix P R).mulVec (x ∘ ec.symm) =
      (groupedLeadingMatrix P R).mulVec (y ∘ ec.symm) := by
    funext i
    obtain ⟨j, rfl⟩ := er.surjective i
    exact congrFun hxy j
  have h := groupedLeadingMatrix_mulVec_injective P R n horth hn hP hR hm
  funext j
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using congrFun h (ec j)

end IdealGeneration.TripleNormal
