module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The base rank condition is open in the free points

A fixed family of vector polynomials is evaluated at free trace points.
A determinant in the free coordinates records the rank witness, after
reindexing the columns by the supplied row-column equivalence.
-/

noncomputable section
namespace IdealGeneration.TripleNormal

open Matrix MvPolynomial

variable {K V I J : Type*} [Field K] [Fintype I] [Fintype J] {r : ℕ}

/-- Evaluate the chosen components of the vector polynomials at the
corresponding free trace points. -/
def freeTraceMatrix (rowPoint : I → Fin r) (rowCoordinate : I → Fin 3)
    (f : J → Fin 3 → MvPolynomial V K) (a : Fin r × V → K) : Matrix I J K :=
  Matrix.of fun i j => eval (fun v => a (rowPoint i, v)) (f j (rowCoordinate i))

private theorem injective_mulVec_iff_submatrix_det_ne_zero (ec : I ≃ J) (M : Matrix I J K)
    [DecidableEq I] :
    Function.Injective M.mulVec ↔ (M.submatrix id ec).det ≠ 0 := by
  constructor
  · intro hM
    have hs : Function.Injective (M.submatrix id ec).mulVec := by
      intro u v huv
      have he : M.mulVec (u ∘ ec.symm) = M.mulVec (v ∘ ec.symm) := by
        simpa only [submatrix_mulVec_equiv, Function.comp_id] using huv
      have h := hM he
      funext i
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using congrFun h (ec i)
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hs))
  · intro hM u v huv
    have hs := Matrix.mulVec_injective_of_det_ne_zero hM
    have he : (M.submatrix id ec).mulVec (u ∘ ec) =
        (M.submatrix id ec).mulVec (v ∘ ec) := by
      simpa only [submatrix_mulVec_equiv, Function.comp_id, Function.comp_assoc,
        Equiv.self_comp_symm] using huv
    have h := hs he
    funext j
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun h (ec.symm j)

/-- An injective evaluation witness gives a nonempty principal open in
the free trace coordinates on which the actual evaluation stays injective. -/
theorem freeTraceMatrix_injective_principal_open (ec : I ≃ J)
    (rowPoint : I → Fin r) (rowCoordinate : I → Fin 3)
    (f : J → Fin 3 → MvPolynomial V K) (a₀ : Fin r × V → K)
    (h₀ : Function.Injective (freeTraceMatrix rowPoint rowCoordinate f a₀).mulVec) :
    ∃ P : MvPolynomial (Fin r × V) K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 → Function.Injective (freeTraceMatrix rowPoint rowCoordinate f a).mulVec := by
  classical
  let B : Matrix I I (MvPolynomial (Fin r × V) K) :=
    Matrix.of fun i j => rename (fun v => (rowPoint i, v)) (f (ec j) (rowCoordinate i))
  have hB (a : Fin r × V → K) :
      eval a B.det = ((freeTraceMatrix rowPoint rowCoordinate f a).submatrix id ec).det := by
    rw [(eval a).map_det]
    congr 1
    ext i j
    change eval a (rename (fun v => (rowPoint i, v)) (f (ec j) (rowCoordinate i))) = _
    exact eval_rename_prod_mk a (rowPoint i) (f (ec j) (rowCoordinate i))
  refine ⟨B.det, ?_, fun a ha => ?_⟩
  · rw [hB]
    exact (injective_mulVec_iff_submatrix_det_ne_zero ec _).mp h₀
  · rw [hB] at ha
    exact (injective_mulVec_iff_submatrix_det_ne_zero ec _).mpr ha

end IdealGeneration.TripleNormal
