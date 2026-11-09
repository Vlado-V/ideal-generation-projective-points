module

public import IdealGeneration.CubicB11Assembly
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Tactic.NormNum

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The pool columns of the B.11 block and their exact enumeration. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

/-- The B.7 columns whose support is assigned to the initial pool. -/
abbrev PoolColumn (k : ℕ) := {c : B7Column (10 + 2 * k) // b7Owner c = none}

private abbrev BaseSingle := {e : Edge 10 // single e = true}
private abbrev BaseNeighbor (b : Fin 2) := {i : Fin 10 // neighbor b i}

private theorem card_baseSingle : Fintype.card BaseSingle = 2 := by decide +kernel
private theorem card_baseNeighbor_zero : Fintype.card (BaseNeighbor 0) = 4 := by decide +kernel
private theorem card_baseNeighbor_one : Fintype.card (BaseNeighbor 1) = 3 := by decide +kernel

private theorem neighbor_pool_iff {k : ℕ} (b : Fin 2) (i : Fin (10 + 2 * k))
    (hi : i.val < 10) : neighbor b i ↔ neighbor b (⟨i.val, hi⟩ : Fin 10) := by
  fin_cases b <;> simp [neighbor, singleLabels] <;> omega

private def liftPoolSingle (k : ℕ) (e : BaseSingle) :
    {e : Edge (10 + 2 * k) // single e = true} :=
  ⟨⟨(e.val.val.1.castAdd (2 * k), e.val.val.2.castAdd (2 * k)), e.val.property⟩, e.property⟩

private def readPoolSingle {k : ℕ} (e : {e : Edge (10 + 2 * k) // single e = true})
    (h₁ : e.val.val.1.val < 10) (h₂ : e.val.val.2.val < 10) : BaseSingle :=
  ⟨⟨(⟨e.val.val.1.val, h₁⟩, ⟨e.val.val.2.val, h₂⟩), e.val.property⟩, e.property⟩

private def liftPoolNeighbor (k : ℕ) (b : Fin 2) (i : BaseNeighbor b) :
    {j : Fin (10 + 2 * k) // neighbor b j} :=
  ⟨i.val.castAdd (2 * k),
    (neighbor_pool_iff b (i.val.castAdd (2 * k)) i.val.isLt).mpr i.property⟩

private def readPoolNeighbor {k : ℕ} {b : Fin 2} (i : {j : Fin (10 + 2 * k) // neighbor b j})
    (hi : i.val.val < 10) : BaseNeighbor b :=
  ⟨⟨i.val.val, hi⟩, (neighbor_pool_iff b i.val hi).mp i.property⟩

private theorem b7Owner_local_none_iff {m : ℕ} (b : Fin 2) (c : LocalColumn m b) :
    b7Owner (.localColumn b c) = none ↔
      (localEndpoints c).1.val < 10 ∧ (localEndpoints c).2.val < 10 := by
  change faceOwner (monomialFace (localEndpoints c).1 (localEndpoints c).2) = none ↔ _
  rw [faceOwner_eq_none, faceVertices_monomialFace]
  constructor
  · intro h
    exact ⟨h _ (by simp), h _ (by simp)⟩
  · rintro ⟨h₁, h₂⟩ j hj
    rcases (show j = (localEndpoints c).1 ∨ j = (localEndpoints c).2 from by simpa using hj)
      with rfl | rfl
    · exact h₁
    · exact h₂

/-- Pool labels split by the old edge, local cross, motion, extra and remaining families. -/
private abbrev PoolLabel :=
  ((Fin 2 × BaseSingle) ⊕ (Σ b : Fin 2, BaseNeighbor b × Fin 10)) ⊕
    (Fin 2 × Fin 10 × Fin 3) ⊕ (Σ b : Fin 2, BaseNeighbor b × Fin 2) ⊕
    (Fin 2 × Fin 2 × Fin 3)

private def poolLabelToColumn (k : ℕ) : PoolLabel → PoolColumn k
  | .inl (.inl (b, e)) => ⟨.localColumn b (.inl (liftPoolSingle k e)),
      (b7Owner_local_none_iff b _).mpr ⟨e.val.val.1.isLt, e.val.val.2.isLt⟩⟩
  | .inl (.inr ⟨b, i, j⟩) => ⟨.localColumn b (.inr (liftPoolNeighbor k b i, j.castAdd (2 * k))),
      (b7Owner_local_none_iff b _).mpr ⟨i.val.isLt, j.isLt⟩⟩
  | .inr (.inl (b, i, q)) => ⟨.motion b (i.castAdd (2 * k)) q,
      (vertexOwner_eq_none _).mpr i.isLt⟩
  | .inr (.inr (.inl ⟨b, i, u⟩)) => ⟨.extra b (liftPoolNeighbor k b i) u,
      (vertexOwner_eq_none _).mpr i.val.isLt⟩
  | .inr (.inr (.inr (b, u, q))) => ⟨.remaining b u q, rfl⟩

private def poolColumnToLabel {k : ℕ} : PoolColumn k → PoolLabel
  | ⟨.localColumn b (.inl e), h⟩ =>
      let he := (b7Owner_local_none_iff b (.inl e)).mp h
      .inl (.inl (b, readPoolSingle e he.1 he.2))
  | ⟨.localColumn b (.inr (i, j)), h⟩ =>
      let hij := (b7Owner_local_none_iff b (.inr (i, j))).mp h
      .inl (.inr ⟨b, readPoolNeighbor i hij.1, ⟨j.val, hij.2⟩⟩)
  | ⟨.motion b i q, h⟩ => .inr (.inl (b, ⟨i.val, (vertexOwner_eq_none i).mp h⟩, q))
  | ⟨.extra b i u, h⟩ => .inr (.inr (.inl ⟨b,
      readPoolNeighbor i ((vertexOwner_eq_none i.val).mp h), u⟩))
  | ⟨.remaining b u q, _⟩ => .inr (.inr (.inr (b, u, q)))

private def poolColumnEquiv (k : ℕ) : PoolLabel ≃ PoolColumn k where
  toFun := poolLabelToColumn k
  invFun := poolColumnToLabel
  left_inv := by
    rintro ((⟨b, e⟩ | ⟨b, i, j⟩) | (⟨b, i, q⟩ | (⟨b, i, u⟩ | ⟨b, u, q⟩))) <;> rfl
  right_inv := by
    rintro ⟨c, h⟩
    cases c with
    | localColumn b c => rcases c with e | ⟨i, j⟩ <;> rfl
    | motion b i q => rfl
    | extra b i u => rfl
    | remaining b u q => rfl

instance (k : ℕ) : Fintype (PoolColumn k) := Fintype.ofEquiv PoolLabel (poolColumnEquiv k)

/-- The five families contribute `4 + 70 + 60 + 14 + 12` pool columns. -/
theorem card_poolColumn (k : ℕ) : Fintype.card (PoolColumn k) = 160 := by
  rw [← Fintype.card_congr (poolColumnEquiv k)]
  norm_num [PoolLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma, Fin.sum_univ_two,
    card_baseSingle, card_baseNeighbor_zero, card_baseNeighbor_one]

/-- An injective pool enumeration of the right size covers all unowned columns. -/
theorem poolColumn_coverage {ι : Type*} [Fintype ι] {k : ℕ}
    (column : ι → B7Column (10 + 2 * k)) (hcard : Fintype.card ι = 160)
    (hpool : ∀ i, b7Owner (column i) = none) (hinj : Function.Injective column) :
    ∀ c, b7Owner c = none → c ∈ Set.range column := by
  let f : ι → PoolColumn k := fun i => ⟨column i, hpool i⟩
  have hf : Function.Injective f := fun _ _ h => hinj (congrArg Subtype.val h)
  have hsize : Fintype.card ι = Fintype.card (PoolColumn k) := hcard.trans (card_poolColumn k).symm
  have hsurj := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hsize⟩).2
  intro c hc
  obtain ⟨i, hi⟩ := hsurj ⟨c, hc⟩
  exact ⟨i, congrArg Subtype.val hi⟩

/-- A nonsingular pool matrix cannot repeat a column label. -/
theorem poolColumn_injective_of_det {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {k : ℕ} (P : B7Data K (10 + 2 * k)) (R : PoolBlockData K (10 + 2 * k) ι)
    (hdet : (poolMatrix P R).det ≠ 0) : Function.Injective R.column := by
  intro i j hij
  apply (Matrix.linearIndependent_cols_of_det_ne_zero hdet).injective
  funext r
  change probeEntry P (R.probe r) (R.column i) = probeEntry P (R.probe r) (R.column j)
  rw [hij]

/-- Nonsingularity of the 160-column pool block supplies its coverage certificate. -/
theorem poolColumn_coverage_of_det {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {k : ℕ} (P : B7Data K (10 + 2 * k)) (R : PoolBlockData K (10 + 2 * k) ι)
    (hcard : Fintype.card ι = 160) (hdet : (poolMatrix P R).det ≠ 0) :
    ∀ c, b7Owner c = none → c ∈ Set.range R.column :=
  poolColumn_coverage R.column hcard R.columnPool (poolColumn_injective_of_det P R hdet)

end IdealGeneration.CubicSupported.B5
