module

public import IdealGeneration.GeneratorDimensions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Minimal homogeneous generating families for the actual point ideal. -/

noncomputable section
namespace IdealGeneration

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n p d : ℕ}

local instance pointPieceGroup (a : PointCoordinates K n p) (e : ℕ) :
    AddCommGroup (pointDegreePiece K a e) := Module.addCommMonoidToAddCommGroup K

/-- The new generators in the next degree are classes modulo linear multiples of initial equations. -/
abbrev PointNextGeneratorSpace (a : PointCoordinates K n p) (d : ℕ) :=
  (pointDegreePiece K a (d + 1)) ⧸ (pointMultiplication a d).range

private def pieceToPoly (a : PointCoordinates K n p) (e : ℕ) :
    pointDegreePiece K a e →ₗ[K] Poly K (n + 1) :=
  (Forms K (n + 1) e).subtype.comp (pointDegreePiece K a e).subtype

private theorem pieceToPoly_injective (a : PointCoordinates K n p) (e : ℕ) :
    Function.Injective (pieceToPoly a e) := fun _ _ h => Subtype.ext (Subtype.ext h)

private theorem pieceToPoly_mem (a : PointCoordinates K n p) (e : ℕ) (f : pointDegreePiece K a e) :
    pieceToPoly a e f ∈ pointIdeal K a :=
  (homogeneous_mem_pointIdeal_iff a f.val).mpr f.property

private theorem pieceToPoly_homogeneous (a : PointCoordinates K n p) (e : ℕ)
    (f : pointDegreePiece K a e) : (pieceToPoly a e f).IsHomogeneous e := f.val.property

private theorem ideal_smul_mem (J : Ideal (Poly K (n + 1))) (c : K) {f : Poly K (n + 1)}
    (hf : f ∈ J) : c • f ∈ J := by
  rw [smul_eq_C_mul]
  exact J.mul_mem_left _ hf

/-- The polynomial family consisting of the initial basis and the lifted quotient basis. -/
def twoDegreeGeneratorFamily (a : PointCoordinates K n p) (d : ℕ) {α β : Type*}
    (u : α → pointDegreePiece K a d) (v : β → pointDegreePiece K a (d + 1)) :
    α ⊕ β → Poly K (n + 1) :=
  Sum.elim (pieceToPoly a d ∘ u) (pieceToPoly a (d + 1) ∘ v)

@[simp] theorem twoDegreeGeneratorFamily_inl (a : PointCoordinates K n p) (d : ℕ) {α β : Type*}
    (u : α → pointDegreePiece K a d) (v : β → pointDegreePiece K a (d + 1)) (i : α) :
    twoDegreeGeneratorFamily a d u v (.inl i) = (u i).val.val := rfl

@[simp] theorem twoDegreeGeneratorFamily_inr (a : PointCoordinates K n p) (d : ℕ) {α β : Type*}
    (u : α → pointDegreePiece K a d) (v : β → pointDegreePiece K a (d + 1)) (i : β) :
    twoDegreeGeneratorFamily a d u v (.inr i) = (v i).val.val := rfl

private theorem twoDegreeGeneratorFamily_mem (a : PointCoordinates K n p) (d : ℕ) {α β : Type*}
    (u : α → pointDegreePiece K a d) (v : β → pointDegreePiece K a (d + 1)) (i : α ⊕ β) :
    twoDegreeGeneratorFamily a d u v i ∈ pointIdeal K a := by
  rcases i with i | i
  · exact pieceToPoly_mem a d (u i)
  · exact pieceToPoly_mem a (d + 1) (v i)

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A basis of the initial equations and any lifts of a quotient basis generate the point ideal
when its homogeneous equations in the two degrees generate it. -/
theorem pointIdeal_span_basis_and_lifts (a : PointCoordinates K n p) (d : ℕ)
    (hgen : pointIdeal K a = Ideal.span (twoDegreePointEquations a d))
    (B : Basis α K (pointDegreePiece K a d)) (D : Basis β K (PointNextGeneratorSpace a d))
    (v : β → pointDegreePiece K a (d + 1))
    (hv : ∀ i, (pointMultiplication a d).range.mkQ (v i) = D i) :
    Ideal.span (Set.range (twoDegreeGeneratorFamily a d B v)) = pointIdeal K a := by
  let J := Ideal.span (Set.range (twoDegreeGeneratorFamily a d B v))
  have hJ₀ (i : α) : pieceToPoly a d (B i) ∈ J :=
    Ideal.subset_span ⟨Sum.inl i, rfl⟩
  have hJ₁ (i : β) : pieceToPoly a (d + 1) (v i) ∈ J :=
    Ideal.subset_span ⟨Sum.inr i, rfl⟩
  have h₀ (f : pointDegreePiece K a d) : pieceToPoly a d f ∈ J := by
    have he := congrArg (pieceToPoly a d) (B.sum_repr f)
    simp only [map_sum, map_smul] at he
    rw [← he]
    exact J.sum_mem fun i _ => ideal_smul_mem J _ (hJ₀ i)
  have h₁ (f : pointDegreePiece K a (d + 1)) : pieceToPoly a (d + 1) f ∈ J := by
    let q := (pointMultiplication a d).range.mkQ
    let w := ∑ i, D.repr (q f) i • v i
    have hw : q w = q f := by simp [w, q, map_sum, hv]
    have hwJ : pieceToPoly a (d + 1) w ∈ J := by
      simp only [w, map_sum, map_smul]
      exact J.sum_mem fun i _ => ideal_smul_mem J _ (hJ₁ i)
    let z := f + (-1 : K) • w
    have hsub : z ∈ (pointMultiplication a d).range := by
      rw [← Submodule.ker_mkQ (pointMultiplication a d).range, LinearMap.mem_ker]
      change q z = 0
      simp [z, hw]
    obtain ⟨g, hg⟩ := hsub
    have hgJ : pieceToPoly a (d + 1) z ∈ J := by
      rw [← hg]
      change (∑ i, X i * pieceToPoly a d (g i)) ∈ J
      exact J.sum_mem fun i _ => J.mul_mem_left _ (h₀ (g i))
    have hcancel : (-1 : K) • w + w = 0 := by
      calc
        _ = (-1 : K) • w + (1 : K) • w := by rw [one_smul]
        _ = 0 := by rw [← add_smul, neg_add_cancel, zero_smul]
    have hz : z + w = f := by
      change f + (-1 : K) • w + w = f
      rw [add_assoc, hcancel, add_zero]
    have he := congrArg (pieceToPoly a (d + 1)) hz
    rw [map_add] at he
    rw [← he]
    exact J.add_mem hgJ hwJ
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    exact twoDegreeGeneratorFamily_mem a d B v i
  · rw [hgen]
    apply Ideal.span_le.mpr
    rintro f ⟨hf | hf, hI⟩
    · exact h₀ ⟨⟨f, hf⟩, (homogeneous_mem_pointIdeal_iff a ⟨f, hf⟩).mp hI⟩
    · exact h₁ ⟨⟨f, hf⟩, (homogeneous_mem_pointIdeal_iff a ⟨f, hf⟩).mp hI⟩

private theorem homogeneousComponent_mul_right {q f : Poly K (n + 1)} {e t : ℕ}
    (hf : f.IsHomogeneous e) : homogeneousComponent t (q * f) =
      if e ≤ t then homogeneousComponent (t - e) q * f else 0 := by
  simpa only [DirectSum.decompose, Equiv.coe_fn_mk, decomposition.decompose'_apply] using
    (DirectSum.coe_decompose_mul_of_right_mem (fun z => Forms K (n + 1) z) (a := q) t hf)

private theorem coefficients_without_index {ι : Type*} [Fintype ι] (f : ι → Poly K (n + 1)) (i : ι)
    (hi : f i ∈ Ideal.span (f '' {j | j ≠ i})) :
    ∃ c : ι → Poly K (n + 1), c i = 0 ∧ (∑ j, c j * f j) = f i := by
  classical
  let s := Finset.univ.erase i
  have hs : (↑s : Set ι) = {j | j ≠ i} := by ext j; simp [s]
  rw [← hs] at hi
  rw [Set.image_eq_range] at hi
  obtain ⟨r, hr⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
  let c (j : ι) := if h : j ∈ s then r ⟨j, h⟩ else 0
  have hzero (j : ι) (hj : j ∉ s) : c j = 0 := by simp [c, hj]
  refine ⟨c, hzero i (by simp [s]), ?_⟩
  calc
    (∑ j, c j * f j) = ∑ j ∈ s, c j * f j := by
      symm
      exact Finset.sum_subset (Finset.subset_univ s) fun j _ hj => by simp [hzero j hj]
    _ = f i := by
      rw [← Finset.sum_coe_sort]
      simpa [c] using hr

private def multiplyLinearPiece (a : PointCoordinates K n p) (l : Forms K (n + 1) 1)
    (f : pointDegreePiece K a d) : pointDegreePiece K a (d + 1) := by
  let z : Forms K (n + 1) (d + 1) := ⟨l.val * f.val.val, by
    change (l.val * f.val.val).IsHomogeneous (d + 1)
    simpa only [Nat.add_comm 1 d] using l.property.mul f.val.property⟩
  refine ⟨z, (homogeneous_mem_pointIdeal_iff a z).mp ?_⟩
  exact (pointIdeal K a).mul_mem_left l.val (pieceToPoly_mem a d f)

private theorem multiplyLinearPiece_range [CharZero K] (a : PointCoordinates K n p)
    (l : Forms K (n + 1) 1) (f : pointDegreePiece K a d) :
    multiplyLinearPiece a l f ∈ (pointMultiplication a d).range := by
  obtain ⟨u, hu⟩ := formMultiplication_surjective (K := K) (n + 1) 0 l
  have hc (i : Fin (n + 1)) : (u i).val = C ((u i).val.coeff 0) := by
    exact (homogeneousComponent_eq_self (u i).property).symm.trans (homogeneousComponent_zero _)
  refine ⟨fun i => (u i).val.coeff 0 • f, pieceToPoly_injective a (d + 1) ?_⟩
  change (∑ i, X i * ((u i).val.coeff 0 • f.val.val)) = l.val * f.val.val
  have he := congrArg Subtype.val hu
  change (∑ i, X i * (u i).val) = l.val at he
  rw [← he, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_eq_C_mul, mul_assoc, ← hc i]

/-- The basis and lifted quotient basis form an irredundant generating family. -/
theorem twoDegreeGeneratorFamily_indispensable [CharZero K] (a : PointCoordinates K n p) (d : ℕ)
    (B : Basis α K (pointDegreePiece K a d)) (D : Basis β K (PointNextGeneratorSpace a d))
    (v : β → pointDegreePiece K a (d + 1))
    (hv : ∀ i, (pointMultiplication a d).range.mkQ (v i) = D i)
    (i : α ⊕ β) : twoDegreeGeneratorFamily a d B v i ∉
      Ideal.span (twoDegreeGeneratorFamily a d B v '' {j | j ≠ i}) := by
  classical
  intro hi
  obtain ⟨c, hci, hc⟩ := coefficients_without_index (twoDegreeGeneratorFamily a d B v) i hi
  rcases i with i | i
  · have h := congrArg (homogeneousComponent d) hc
    simp only [map_sum, map_add, Fintype.sum_sum_type, twoDegreeGeneratorFamily_inl, twoDegreeGeneratorFamily_inr,
      homogeneousComponent_mul_right (hf := (B _).val.property),
      homogeneousComponent_mul_right (hf := (v _).val.property), le_refl, ite_true,
      Nat.sub_self, homogeneousComponent_zero, Nat.not_succ_le_self, ite_false, Finset.sum_const_zero,
      add_zero, homogeneousComponent_eq_self (B i).val.property, ← smul_eq_C_mul] at h
    have hb : (∑ j, (c (.inl j)).coeff 0 • B j) = B i := by
      apply pieceToPoly_injective a d
      simp only [map_sum, map_smul]
      exact h
    have hz := congrArg (fun z => B.repr z i) hb
    rw [Basis.repr_sum_self, Basis.repr_self] at hz
    simp [hci] at hz
  · let L (j : α) : Forms K (n + 1) 1 :=
      ⟨homogeneousComponent 1 (c (.inl j)), homogeneousComponent_isHomogeneous _ _⟩
    let w := ∑ j, multiplyLinearPiece a (L j) (B j)
    have h := congrArg (homogeneousComponent (d + 1)) hc
    have hsub : d + 1 - d = 1 := by omega
    simp only [map_sum, map_add, Fintype.sum_sum_type, twoDegreeGeneratorFamily_inl, twoDegreeGeneratorFamily_inr,
      homogeneousComponent_mul_right (hf := (B _).val.property),
      homogeneousComponent_mul_right (hf := (v _).val.property), Nat.le_succ, le_refl, ite_true,
      hsub, Nat.sub_self, homogeneousComponent_zero,
      homogeneousComponent_eq_self (v i).val.property, ← smul_eq_C_mul] at h
    have hb : w + ∑ j, (c (.inr j)).coeff 0 • v j = v i := by
      apply pieceToPoly_injective a (d + 1)
      simp only [w, map_add, map_sum, map_smul]
      exact h
    have hw : w ∈ (pointMultiplication a d).range :=
      (pointMultiplication a d).range.sum_mem (fun j _ => multiplyLinearPiece_range a (L j) (B j))
    have hwq : (pointMultiplication a d).range.mkQ w = 0 := by
      rw [← Submodule.ker_mkQ (pointMultiplication a d).range] at hw
      exact LinearMap.mem_ker.mp hw
    have hq := congrArg ((pointMultiplication a d).range.mkQ) hb
    simp only [map_add, map_sum, map_smul, hwq, hv, zero_add] at hq
    have hz := congrArg (fun z => D.repr z i) hq
    rw [Basis.repr_sum_self, Basis.repr_self] at hz
    simp [hci] at hz

/-- Indispensability makes the index count an actual count of distinct equations. -/
theorem injective_of_indispensable {ι : Type*} (g : ι → Poly K (n + 1))
    (h : ∀ i, g i ∉ Ideal.span (g '' {j | j ≠ i})) : Function.Injective g := by
  intro i j he
  by_contra hij
  apply h i
  apply Ideal.subset_span
  exact ⟨j, Ne.symm hij, he.symm⟩

/-- The two generator counts are realized by a distinct minimal homogeneous family. -/
theorem pointIdeal_exact_minimal_generators [CharZero K]
    (a : PointCoordinates K n p) (d : ℕ) (hd : 1 ≤ d)
    (hp0 : N (n + 1) (d - 1) ≤ p) (hp1 : p ≤ N (n + 1) d)
    (hpost : ∀ e, pointHilbertFunction K a e = min (N (n + 1) e) p)
    (hm : HasMaximalRank (pointMultiplication a d)) :
    ∃ r : ℕ, (r : ℚ) = max 0 ((n : ℚ) * (E (n + 1) d - (N (n + 1) d - p : ℕ))) ∧
      ∃ g : Fin (N (n + 1) d - p) ⊕ Fin r → Poly K (n + 1),
        (∀ i, (g (.inl i)).IsHomogeneous d) ∧
        (∀ i, (g (.inr i)).IsHomogeneous (d + 1)) ∧
        Ideal.span (Set.range g) = pointIdeal K a ∧
        (∀ i, g i ∉ Ideal.span (g '' {j | j ≠ i})) ∧ Function.Injective g := by
  have : Module.Free K (pointDegreePiece K a d) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (pointDegreePiece K a d)
  have : Module.Free K (PointNextGeneratorSpace a d) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (PointNextGeneratorSpace a d)
  let B := Module.finBasisOfFinrankEq K (pointDegreePiece K a d)
    (pointDegreePiece_finrank a (hpost d))
  let D := Module.finBasis K (PointNextGeneratorSpace a d)
  choose v hv using fun i => (pointMultiplication a d).range.mkQ_surjective (D i)
  let g := twoDegreeGeneratorFamily a d B v
  have hminimal := twoDegreeGeneratorFamily_indispensable a d B D v hv
  refine ⟨finrank K (PointNextGeneratorSpace a d),
    point_next_generator_dimension a hp1 (hpost d) (hpost (d + 1)) hm,
    g, ?_, ?_, ?_, hminimal, injective_of_indispensable g hminimal⟩
  · intro i
    exact pieceToPoly_homogeneous a d (B i)
  · intro i
    exact pieceToPoly_homogeneous a (d + 1) (v i)
  · exact pointIdeal_span_basis_and_lifts a d (pointIdeal_eq_span_two_degrees a d hd hpost hp0 hp1) B D v hv

end IdealGeneration
