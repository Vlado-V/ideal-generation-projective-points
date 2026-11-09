module

public import IdealGeneration.TripleNormalConic
public import IdealGeneration.PointAvoidance

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Simultaneous nonvanishing of the chord determinants in the three-normal step. -/

namespace IdealGeneration.TripleNormal
open Matrix MvPolynomial
open scoped Matrix

variable {K : Type*} [Field K] {I J : Type*}

/-- A chord has endpoints among the old base variables and the three new ones. -/
abbrev Chord (I : Type*) := (I ⊕ Fin 3) × (I ⊕ Fin 3)

/-- The rows of the chord matrix are normals with the endpoint difference removed. -/
def chordMatrix (t : I → K) (u : Fin 3 → K) (e : Fin 3 → Chord I) : Matrix (Fin 3) (Fin 3) K :=
  fun j => chordNormal (Sum.elim t u (e j).1) (Sum.elim t u (e j).2)

/-- The determinant is polynomial in the three new endpoint parameters. -/
noncomputable def chordDetPolynomial (t : I → K) (e : Fin 3 → Chord I) :
    MvPolynomial (Fin 3) K :=
  let p := Sum.elim (fun i => C (t i)) (X : Fin 3 → MvPolynomial (Fin 3) K)
  (Matrix.of fun j : Fin 3 =>
    ![p (e j).1 * p (e j).2, -(p (e j).1 + p (e j).2), 1]).det

@[simp] theorem eval_chordDetPolynomial (t : I → K) (u : Fin 3 → K) (e : Fin 3 → Chord I) :
    eval u (chordDetPolynomial t e) = (chordMatrix t u e).det := by
  let p := Sum.elim (fun i => C (t i)) (X : Fin 3 → MvPolynomial (Fin 3) K)
  have hp (a : I ⊕ Fin 3) : eval u (p a) = Sum.elim t u a := by
    cases a <;> simp [p]
  unfold chordDetPolynomial
  change eval u (Matrix.of (fun j : Fin 3 =>
    ![p (e j).1 * p (e j).2, -(p (e j).1 + p (e j).2), 1])).det = _
  rw [(eval u).map_det]
  congr 1
  ext i j
  fin_cases j <;> simp [chordMatrix, chordNormal, hp]

/-- The normals of the three sides of a conic triangle are independent. -/
theorem chordNormal_triangle_det (a b c : K) :
    (Matrix.det (Matrix.of ![chordNormal a b, chordNormal b c, chordNormal c a])) =
      (b - a) * (c - b) * (a - c) := by
  simp [Matrix.det_fin_three, chordNormal]
  ring

private theorem triangle_det_ne_zero {a b c : K}
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (Matrix.det (Matrix.of ![chordNormal a b, chordNormal b c, chordNormal c a])) ≠ 0 := by
  rw [chordNormal_triangle_det]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hbc.symm))
    (sub_ne_zero.mpr hca.symm)

private def cycleThree : Fin 3 → Fin 3 := ![1, 2, 0]

/-- A matching of three old vertices to the three new vertices admits a
triangle specialization. For this individual polynomial witness the new
parameters can coincide with the old parameters. -/
theorem matching_chord_witness (t : I → K) (a : Fin 3 → I) (b : Fin 3 ≃ Fin 3)
    (h₀₁ : t (a 0) ≠ t (a 1)) (h₁₂ : t (a 1) ≠ t (a 2)) (h₂₀ : t (a 2) ≠ t (a 0)) :
    ∃ u : Fin 3 → K,
      (chordMatrix t u (fun j => (.inl (a j), .inr (b j)))).det ≠ 0 := by
  let u : Fin 3 → K := fun j => t (a (cycleThree (b.symm j)))
  refine ⟨u, ?_⟩
  have hm : chordMatrix t u (fun j => (.inl (a j), .inr (b j))) =
      ![chordNormal (t (a 0)) (t (a 1)),
        chordNormal (t (a 1)) (t (a 2)),
        chordNormal (t (a 2)) (t (a 0))] := by
    ext i j
    fin_cases i <;> simp [chordMatrix, u, cycleThree]
  rw [hm]
  exact triangle_det_ne_zero h₀₁ h₁₂ h₂₀

/-- The triangle formed by the three new vertices has a nonzero specialization. -/
theorem new_triangle_chord_witness [CharZero K] (t : I → K) :
    ∃ u : Fin 3 → K,
      (chordMatrix t u (fun j => (.inr j, .inr (cycleThree j)))).det ≠ 0 := by
  let u : Fin 3 → K := ![0, 1, 2]
  refine ⟨u, ?_⟩
  have hm : chordMatrix t u (fun j => (.inr j, .inr (cycleThree j))) =
      ![chordNormal (0 : K) 1, chordNormal 1 2, chordNormal 2 0] := by
    ext i j
    fin_cases i <;> simp [chordMatrix, u, cycleThree]
  rw [hm]
  exact triangle_det_ne_zero (by norm_num) (by norm_num) (by norm_num)

/-- The first and last triples in the sorted old-new list. -/
def boundaryChords (last : Bool) (a b : I) (v w : Fin 3) : Fin 3 → Chord I :=
  if last then
    ![(.inl a, .inr w), (.inl b, .inr v), (.inl a, .inr v)]
  else
    ![(.inl a, .inr v), (.inl b, .inr v), (.inl a, .inr w)]

private theorem boundary_det_ne_zero (last : Bool) {a b d : K}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    (if last then Matrix.det (Matrix.of ![chordNormal a b, chordNormal b d, chordNormal a d])
      else Matrix.det (Matrix.of ![chordNormal a d, chordNormal b d, chordNormal a b])) ≠ 0 := by
  have h : chordNormal d a = chordNormal a d := by
    simp [chordNormal, mul_comm, add_comm]
  cases last
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have he : (Matrix.det (Matrix.of ![chordNormal a d, chordNormal b d, chordNormal a b])) =
        -((b - a) * (d - b) * (a - d)) := by
      simp [Matrix.det_fin_three, chordNormal]
      ring
    rw [he, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hbd.symm))
      (sub_ne_zero.mpr had)
  · simpa only [↓reduceIte, h] using triangle_det_ne_zero hab hbd had.symm

/-- In either boundary triple, the single new endpoint can specialize to
the other old endpoint, making a triangle with the common new endpoint. -/
theorem boundary_chord_witness [Infinite K] (t : I → K) (last : Bool)
    {a b : I} {v w : Fin 3} (hab : t a ≠ t b) (hvw : v ≠ w) :
    ∃ u : Fin 3 → K, (chordMatrix t u (boundaryChords last a b v w)).det ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ := Set.Infinite.exists_notMem_finset (Set.infinite_univ : Set.Infinite (Set.univ : Set K))
    ({t a, t b} : Finset K)
  have hda : t a ≠ d := by
    intro h
    exact hd.2 (by simp [h])
  have hdb : t b ≠ d := by
    intro h
    exact hd.2 (by simp [h])
  let u : Fin 3 → K := fun i => if i = v then d else t b
  refine ⟨u, ?_⟩
  have hm : chordMatrix t u (boundaryChords last a b v w) =
      if last then Matrix.of ![chordNormal (t a) (t b), chordNormal (t b) d, chordNormal (t a) d]
      else Matrix.of ![chordNormal (t a) d, chordNormal (t b) d, chordNormal (t a) (t b)] := by
    ext i j
    cases last <;> fin_cases i <;> simp [chordMatrix, boundaryChords, u, hvw.symm]
  rw [hm]
  have he := boundary_det_ne_zero last hab hda hdb
  cases last <;> exact he

private theorem ne_zero_of_eval {p : MvPolynomial (Fin 3) K} (u : Fin 3 → K)
    (h : eval u p ≠ 0) : p ≠ 0 := by
  intro hzero
  exact h (by rw [hzero, map_zero])

private noncomputable def chordFactorPolynomial
    (a b : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2)

@[simp] private theorem eval_chordFactorPolynomial (u : Fin 3 → K)
    (a b : MvPolynomial (Fin 3) K) :
    eval u (chordFactorPolynomial a b) = chordFactor (eval u a) (eval u b) := by
  simp [chordFactorPolynomial, chordFactor]

/-- All the specified chord determinants are nonzero for a common choice
of the three new parameters. The old-new and new-new chord factors and
the new parameters themselves can be kept nonzero at the same choice. -/
theorem exists_chord_parameters [Infinite K] [Fintype I] [Fintype J]
    (t : I → K) (ht : ∀ i, t i ≠ 0) (e : J → Fin 3 → Chord I)
    (h : ∀ j, ∃ u : Fin 3 → K, (chordMatrix t u (e j)).det ≠ 0) :
    ∃ u : Fin 3 → K, (∀ j, u j ≠ 0) ∧
      (∀ i j, chordFactor (t i) (u j) ≠ 0) ∧
      (∀ i j, i ≠ j → chordFactor (u i) (u j) ≠ 0) ∧
      ∀ j, (chordMatrix t u (e j)).det ≠ 0 := by
  classical
  let P₀ : MvPolynomial (Fin 3) K := ∏ i, X i
  let P₁ : MvPolynomial (Fin 3) K := ∏ i, ∏ j : Fin 3, chordFactorPolynomial (C (t i)) (X j)
  let P₂ : MvPolynomial (Fin 3) K :=
    ∏ i : Fin 3, ∏ j : Fin 3, if i = j then 1 else chordFactorPolynomial (X i) (X j)
  let P₃ : MvPolynomial (Fin 3) K := ∏ j, chordDetPolynomial t (e j)
  have h₀ : P₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ _ => X_ne_zero _
  have h₁ : P₁ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    apply ne_zero_of_eval (fun _ => 0)
    rw [eval_chordFactorPolynomial]
    simp [chordFactor, ht i]
  have h₂ : P₂ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    by_cases hij : i = j
    · simp [hij]
    · rw [ite_eq_right hij]
      apply ne_zero_of_eval (fun l => if l = i then 1 else 0)
      simp [chordFactor, Ne.symm hij]
  have h₃ : P₃ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    obtain ⟨u, hu⟩ := h j
    apply ne_zero_of_eval u
    simpa using hu
  have hP : P₀ * P₁ * P₂ * P₃ ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero h₀ h₁) h₂) h₃
  have hex : ∃ u : Fin 3 → K, eval u (P₀ * P₁ * P₂ * P₃) ≠ 0 := by
    by_contra! he
    exact hP (MvPolynomial.funext he)
  obtain ⟨u, hu⟩ := hex
  have hprod : ((eval u P₀ ≠ 0 ∧ eval u P₁ ≠ 0) ∧ eval u P₂ ≠ 0) ∧ eval u P₃ ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using hu
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · simpa [P₀, Finset.prod_ne_zero_iff] using hprod.1.1.1
  · simpa [P₁, Finset.prod_ne_zero_iff] using hprod.1.1.2
  · intro i j hij
    have hi : ∀ i j : Fin 3,
        eval u (if i = j then 1 else chordFactorPolynomial (X i) (X j)) ≠ 0 := by
      simpa only [P₂, map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies] using
        hprod.1.2
    simpa [hij] using hi i j
  · simpa [P₃, Finset.prod_ne_zero_iff] using hprod.2

end IdealGeneration.TripleNormal
