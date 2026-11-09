module

public import IdealGeneration.CubicMarkedBlock
public import IdealGeneration.CubicB4Deformation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Transport of the specialized B.4 block matrix to the actual marked evaluation. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B4

open MvPolynomial B5 B22 Module

variable {K : Type*} [Field K] {m f n l p : ℕ}

/-- The old free supports occupy the first block of the enlarged free list. -/
abbrev oldFreeEmbedding (f n l : ℕ) : Fin f ↪ Fin (f + (n + l)) :=
  Fin.castAddEmb (n + l)

def nearFreeIndex (f l : ℕ) {n : ℕ} (i : Fin n) : Fin (f + (n + l)) :=
  Fin.natAdd f (Fin.castAdd l i)

def farFreeIndex (f n : ℕ) {l : ℕ} (i : Fin l) : Fin (f + (n + l)) :=
  Fin.natAdd f (Fin.natAdd n i)

theorem nearFreeIndex_not_old (i : Fin n) :
    nearFreeIndex f l i ∉ Set.range (oldFreeEmbedding f n l) := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = f + i.val at hv
  have := j.isLt
  omega

theorem farFreeIndex_not_old (i : Fin l) :
    farFreeIndex f n i ∉ Set.range (oldFreeEmbedding f n l) := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = f + (n + i.val) at hv
  have := j.isLt
  omega

/-- Every free row outside the old block belongs to the near or far list. -/
theorem newFreeIndex_cases (i : Fin (f + (n + l))) :
    i ∉ Set.range (oldFreeEmbedding f n l) →
      (∃ j : Fin n, nearFreeIndex f l j = i) ∨ (∃ j : Fin l, farFreeIndex f n j = i) := by
  refine Fin.addCases (fun j hj => (hj ⟨j, rfl⟩).elim) (fun j _ => ?_) i
  exact Fin.addCases (fun a => Or.inl ⟨a, rfl⟩) (fun b => Or.inr ⟨b, rfl⟩) j

/-- The actual enlarged free list at a specialized motion parameter. -/
def enlargedFree (old : Fin f → Fin m → K)
    (nearPoint : Fin n → Fin m → K) (nearWeight : Fin n → Fin 2 → K)
    (farPoint : Fin l → Fin (m + 2) → K) (eps : K) :
    Fin (f + (n + l)) → Fin (m + 2) → K :=
  Fin.addCases (fun i => extendTrace (old i))
    (Fin.addCases (fun i => Fin.addCases (nearPoint i) (fun k => nearWeight i k * eps)) farPoint)

variable (old : Fin f → Fin m → K)
variable (nearPoint : Fin n → Fin m → K) (nearWeight : Fin n → Fin 2 → K)
variable (farPoint : Fin l → Fin (m + 2) → K)

local notation "freeAt" => enlargedFree old nearPoint nearWeight farPoint

@[simp] theorem enlargedFree_old (eps : K) (i : Fin f) :
    freeAt eps (oldFreeEmbedding f n l i) = extendTrace (old i) := by
  exact Fin.addCases_left i

@[simp] theorem enlargedFree_near (eps : K) (i : Fin n) :
    freeAt eps (nearFreeIndex f l i) =
      Fin.addCases (nearPoint i) (fun k => nearWeight i k * eps) := by
  simp [enlargedFree, nearFreeIndex]

@[simp] theorem enlargedFree_far (eps : K) (i : Fin l) :
    freeAt eps (farFreeIndex f n i) = farPoint i := by
  simp [enlargedFree, farFreeIndex]

variable {P : Parameters K m} {Q : Parameters K (m + 2)}
variable {A B : Type*}

/-- Enumerate both scalar components at each moving probe. -/
def nearEnumeration (index : A ≃ (Fin n × Fin 2)) : A → B11Probe K m :=
  fun a => ⟨nearPoint (index a).1, nearWeight (index a).1, (index a).2⟩

/-- Enumerate the new edge rows and both components of each fixed free probe. -/
def fixedEnumeration (Q : Parameters K (m + 2)) (farPoint : Fin l → Fin (m + 2) → K)
    (index : B ≃ NewIncidence Q ⊕ (Fin l × Fin 2)) : B → FixedRow Q :=
  fun b => match index b with
  | .inl e => .inl e
  | .inr (i, k) => .inr (farPoint i, k)

/-- The new scalar coordinate space in the actual marked configuration. -/
abbrev NewCoordinates (h : Compatible P Q) (f n l : ℕ) :=
  ({b : Q.SingleEdge // b ∉ Set.range h.singleEdge} → K) ×
  ({i : Fin (f + (n + l)) // i ∉ Set.range (oldFreeEmbedding f n l)} → Fin 2 → K)

variable (h : Compatible P Q)
variable (nearIndex : A ≃ (Fin n × Fin 2))
variable (fixedIndex : B ≃ NewIncidence Q ⊕ (Fin l × Fin 2))

/-- Read the new marked coordinates in the row order of the block matrix. -/
def readNewRows (f : ℕ) : NewCoordinates h f n l →ₗ[K] (A ⊕ B → K) where
  toFun u := fun
    | .inl a => u.2 ⟨nearFreeIndex f l (nearIndex a).1, nearFreeIndex_not_old _⟩ (nearIndex a).2
    | .inr b => match fixedIndex b with
      | .inl e => u.1 ⟨crossSingleEdge Q e, h.crossSingleEdge_not_old e⟩
      | .inr (i, k) => u.2 ⟨farFreeIndex f n i, farFreeIndex_not_old _⟩ k
  map_add' _ _ := by
    funext i
    rcases i with i | i
    · rfl
    · cases hi : fixedIndex i with
      | inl e => simp [hi]
      | inr u =>
        rcases u with ⟨j, k⟩
        simp [hi]
        rfl
  map_smul' _ _ := by
    funext i
    rcases i with i | i
    · rfl
    · cases hi : fixedIndex i with
      | inl e => simp [hi]
      | inr u =>
        rcases u with ⟨j, k⟩
        simp [hi]
        rfl

/-- With a double new-pair edge, the enumerated rows cover all new marked coordinates. -/
theorem readNewRows_injective (f : ℕ) (hpair : Q.single (newPairEdge m) = false) :
    Function.Injective (readNewRows h nearIndex fixedIndex f) := by
  intro u v huv
  apply Prod.ext
  · funext b
    obtain ⟨e, he⟩ := (h.mem_range_crossSingleEdge_iff hpair b.val).mpr b.property
    have hb : (⟨crossSingleEdge Q e, h.crossSingleEdge_not_old e⟩ :
        {b : Q.SingleEdge // b ∉ Set.range h.singleEdge}) = b := Subtype.ext he
    have hu := congrFun huv (.inr (fixedIndex.symm (.inl e)))
    simpa only [readNewRows, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply, hb] using hu
  · funext i k
    rcases newFreeIndex_cases i.val i.property with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hi : (⟨nearFreeIndex f l j, nearFreeIndex_not_old j⟩ :
          {i : Fin (f + (n + l)) // i ∉ Set.range (oldFreeEmbedding f n l)}) = i := Subtype.ext hj
      have hu := congrFun huv (.inl (nearIndex.symm (j, k)))
      simpa only [readNewRows, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply, hi] using hu
    · have hi : (⟨farFreeIndex f n j, farFreeIndex_not_old j⟩ :
          {i : Fin (f + (n + l)) // i ∉ Set.range (oldFreeEmbedding f n l)}) = i := Subtype.ext hj
      have hu := congrFun huv (.inr (fixedIndex.symm (.inr (j, k))))
      simpa only [readNewRows, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply, hi] using hu

variable (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

local notation "nearRows" => nearEnumeration nearPoint nearWeight nearIndex
local notation "fixedRows" => fixedEnumeration Q farPoint fixedIndex
local notation "rowReader" => readNewRows h nearIndex fixedIndex f
local notation "newEval" => h.newMarkedEvaluation (oldFreeEmbedding f n l)

/-- Each moving row reads the corresponding actual free support and component. -/
theorem readNewRows_near_eval (eps : K) (x : h.restrictParameters.ker) (a : A) :
    rowReader (newEval (freeAt eps) h₂ h₆ x) (.inl a) =
      eval (Fin.addCases (nearRows a).point (fun k => (nearRows a).weight k * eps))
        (Q.parameterPhi (freeAt eps) h₂ h₆ x.val (nearRows a).component).val := by
  change (Q.markedEvaluation (freeAt eps) h₂ h₆ x.val).2
    (nearFreeIndex f l (nearIndex a).1) (nearIndex a).2 = _
  rw [Q.markedEvaluation_free, enlargedFree_near]
  rfl

/-- The fixed rows use the actual free and allowed single-edge scalar evaluations. -/
theorem readNewRows_fixed_eval (eps : K) (x : h.restrictParameters.ker) (b : B) :
    rowReader (newEval (freeAt eps) h₂ h₆ x) (.inr b) =
      fixedValue Q (freeAt eps) h₂ h₆ (fixedRows b) x.val := by
  cases hb : fixedIndex b with
  | inl e =>
    simp only [readNewRows, LinearMap.coe_mk, AddHom.coe_mk, hb, fixedEnumeration, fixedValue]
    exact Q.markedEvaluation_singleEdge (freeAt eps) h₂ h₆ x.val (crossSingleEdge Q e)
  | inr u =>
    rcases u with ⟨i, k⟩
    simp only [readNewRows, LinearMap.coe_mk, AddHom.coe_mk, hb, fixedEnumeration, fixedValue]
    change (Q.markedEvaluation (freeAt eps) h₂ h₆ x.val).2 (farFreeIndex f n i) k = _
    rw [Q.markedEvaluation_free, enlargedFree_far]

/-- The polynomial represented by an independent parameter does not depend on the free list. -/
theorem parameterPhi_polynomial_free_irrel {s t : ℕ}
    (F : Fin s → Fin (m + 2) → K) (G : Fin t → Fin (m + 2) → K)
    (x : Q.EliminatedParameters) (k : Fin 2) :
    (Q.parameterPhi F h₂ h₆ x k).val = (Q.parameterPhi G h₂ h₆ x k).val := by
  rw [Q.parameterPhi_polynomial, Q.parameterPhi_polynomial]

private theorem fixedValue_free_irrel {s t : ℕ}
    (F : Fin s → Fin (m + 2) → K) (G : Fin t → Fin (m + 2) → K)
    (r : FixedRow Q) (x : Q.EliminatedParameters) :
    fixedValue Q F h₂ h₆ r x = fixedValue Q G h₂ h₆ r x := by
  rcases r with e | ⟨y, k⟩
  · simp only [fixedValue, parameterPhi_polynomial_free_irrel (Q := Q) h₂ h₆ F G]
  · simp only [fixedValue, parameterPhi_polynomial_free_irrel (Q := Q) h₂ h₆ F G]

private theorem evalRingHom_moving (eps : K) (y : Fin m → K) (w : Fin 2 → K)
    (F : Poly K (m + 2)) : Polynomial.evalRingHom eps (movingEvaluation y w F) =
      eval (Fin.addCases y (fun k => w k * eps)) F :=
  movingEvaluation_aeval y w eps F

variable (hQ : ∀ e, Q.single e = B5.single e)
variable (base : Fin p → Fin (m + 2) → K)
variable (low : A → B7Column m) (high : B → HigherColumn Q)

local notation "deformed" => Matrix.fromBlocks
  (movingLower Q hQ base h₂ h₆ nearRows low) (movingHigher Q base h₂ h₆ nearRows high)
  (fixedLower Q hQ base h₂ h₆ low fixedRows) (fixedHigher Q base h₂ h₆ high fixedRows)

/-- Entrywise identification of the specialized B.4 matrix with the new marked evaluation. -/
theorem specializedBlock_eq_newRows
    (b : Basis (A ⊕ B) K h.restrictParameters.ker)
    (hlow : ∀ j, (b (.inl j)).val = b7Parameter Q hQ (low j))
    (hhigh : ∀ j, (b (.inr j)).val = highParameter Q (high j)) (eps : K) :
    (deformed).map (Polynomial.evalRingHom eps) =
      Matrix.of (fun i j => rowReader (newEval (freeAt eps) h₂ h₆ (b j)) i) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.map_apply, Matrix.fromBlocks_apply₁₁, movingLower, Matrix.of_apply,
      readNewRows_near_eval, hlow]
    rw [← parameterPhi_polynomial_free_irrel (Q := Q) h₂ h₆ base (freeAt eps)]
    exact evalRingHom_moving _ _ _ _
  · simp only [Matrix.map_apply, Matrix.fromBlocks_apply₁₂, movingHigher, Matrix.of_apply,
      readNewRows_near_eval, hhigh]
    rw [← parameterPhi_polynomial_free_irrel (Q := Q) h₂ h₆ base (freeAt eps)]
    exact evalRingHom_moving _ _ _ _
  · simp only [Matrix.map_apply, Matrix.fromBlocks_apply₂₁, fixedLower, Matrix.of_apply,
      readNewRows_fixed_eval, hlow, Polynomial.coe_evalRingHom, Polynomial.eval_C]
    exact fixedValue_free_irrel (Q := Q) h₂ h₆ base (freeAt eps) _ _
  · simp only [Matrix.map_apply, Matrix.fromBlocks_apply₂₂, fixedHigher, Matrix.of_apply,
      readNewRows_fixed_eval, hhigh, Polynomial.coe_evalRingHom, Polynomial.eval_C]
    exact fixedValue_free_irrel (Q := Q) h₂ h₆ base (freeAt eps) _ _

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Nonsingular B.4 diagonal blocks give injectivity of the enlarged marked evaluation. -/
theorem exists_markedEvaluation_injective_of_b4_blocks [Infinite K]
    (b : Basis (A ⊕ B) K h.restrictParameters.ker)
    (hlow : ∀ j, (b (.inl j)).val = b7Parameter Q hQ (low j))
    (hhigh : ∀ j, (b (.inr j)).val = highParameter Q (high j))
    (hold : Function.Injective (P.markedEvaluation old h₂ h₆))
    (h11 : (Matrix.of (fun i j => b7Value (actualB7Data Q) (nearRows i).point
      (nearRows i).weight (nearRows i).component (low j)) : Matrix A A K).det ≠ 0)
    (h22 : (Matrix.of (fun i j => fixedValue Q base h₂ h₆ (fixedRows i)
      (highParameter Q (high j))) : Matrix B B K).det ≠ 0) :
    ∃ eps : K, eps ≠ 0 ∧ Function.Injective (Q.markedEvaluation (freeAt eps) h₂ h₆) := by
  obtain ⟨eps, hε, hdet⟩ := exists_actual_block_det_ne_zero Q hQ base h₂ h₆
    nearRows low high fixedRows h11 h22
  let F := (rowReader).comp (newEval (freeAt eps) h₂ h₆)
  let M := (deformed).map (Polynomial.evalRingHom eps)
  have hM : M = Matrix.of (fun i j => F (b j) i) :=
    specializedBlock_eq_newRows old nearPoint nearWeight farPoint h nearIndex fixedIndex
      h₂ h₆ hQ base low high b hlow hhigh eps
  have hcol : F ∘ b = M.col := by
    rw [hM]
    rfl
  have hli : LinearIndependent K (F ∘ b) := by
    rw [hcol]
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hF : Function.Injective F := by
    rw [← b.constr_self K F]
    exact b.injective_constr_of_linearIndependent hli
  refine ⟨eps, hε, h.markedEvaluation_injective_of_blocks (oldFreeEmbedding f n l)
    old (freeAt eps) h₂ h₆ (enlargedFree_old old nearPoint nearWeight farPoint eps) hold ?_⟩
  intro x y hxy
  apply hF
  exact congrArg rowReader hxy

end IdealGeneration.CubicSupported.B4
