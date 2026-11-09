module

public import IdealGeneration.CubicB11Values
public import IdealGeneration.CubicSupportedRationalChart

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Rational expressions for the actual B.11 entries in primitive and sample parameters. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open Parameters RationalChart CubicRationalFormula

variable {σ : Type*} {m : ℕ}

/-- A row formula lists exactly the trace coordinates on which its sample is supported. -/
structure B11ProbeFormula (σ : Type*) (m : ℕ) where
  support : Finset (Fin m)
  point : Fin m → Formula σ
  weight : Fin 2 → Formula σ
  component : Fin 2

private def basisFormula (q : Fin 3) : Fin 3 → Formula σ := fun r => if r = q then 1 else 0

private def shiftLinearFormula (u : Fin 2) (a : Fin 2 → Formula σ) : Fin 3 → Formula σ :=
  if u = 0 then ![a 0, a 1, 0] else ![0, a 0, a 1]

private def shiftQuadraticFormula (u : Fin 2) (a : Fin 3 → Formula σ) : Fin 4 → Formula σ :=
  if u = 0 then ![a 0, a 1, a 2, 0] else ![0, a 0, a 1, a 2]

private def slopeNormalFormula (a : PrimitiveIndex (m + 2) → Formula σ) (e : Edge (m + 2)) :
    Fin 2 → Formula σ := ![a (.edgeSlope e 0), -1]

/-- Enumerate the support in coordinate order for concrete modular evaluation. -/
def orderedSupportSum (S : Finset (Fin m)) (f : Fin m → Formula σ) : Formula σ :=
  Formula.sumList ((List.finRange m).filter (fun i => decide (i ∈ S))) f

/-- Restrict the linear sum before clearing denominators. -/
def oldLinearValueFormula (a : PrimitiveIndex (m + 2) → Formula σ)
    (s : Edge (m + 2) → Bool) (S : Finset (Fin m)) (y : Fin m → Formula σ)
    (c : Fin (m + 2)) (q : Fin 3 → Formula σ) (r : Fin 2) : Formula σ :=
  orderedSupportSum S fun i => mixedLinearFormula a s c q (Fin.castAdd 2 i) r * y i

/-- The pure correction needs only the diagonal and edges of the row support. -/
def oldPureValueFormula (a : PrimitiveIndex (m + 2) → Formula σ)
    (s : Edge (m + 2) → Bool) (S : Finset (Fin m)) (y : Fin m → Formula σ)
    (q : Fin 4 → Formula σ) (r : Fin 2) : Formula σ :=
  orderedSupportSum S fun i => orderedSupportSum S fun j =>
    upperCoefficientFormula (pureDiagonalFormula a q) (pureOffDiagonalFormula a s q)
      (Fin.castAdd 2 i) (Fin.castAdd 2 j) r * y i * y j

/-- The two mixed corrections and the pure correction in a remaining column. -/
def oldRemainingValueFormula (a : PrimitiveIndex (m + 2) → Formula σ)
    (s : Edge (m + 2) → Bool) (S : Finset (Fin m)) (y : Fin m → Formula σ)
    (c : Fin (m + 2)) (u : Fin 2) (q : Fin 3 → Formula σ) (r : Fin 2) : Formula σ :=
  oldPureValueFormula a s S y (shiftQuadraticFormula u q) r +
    orderedSupportSum S fun i => y i * oldLinearValueFormula a s S y c
      (shiftLinearFormula u (mixedLinearFormula a s c q (Fin.castAdd 2 i))) r

/-- The actual B.7 formulas, with absent coordinate factors eliminated before polynomialization. -/
def b11EntryFormula (a : PrimitiveIndex (m + 2) → Formula σ) (s : Edge (m + 2) → Bool)
    (row : B11ProbeFormula σ m) : B7Column m → Formula σ
  | .localColumn b c =>
      if (localEndpoints c).1 ∈ row.support ∧ (localEndpoints c).2 ∈ row.support then
        row.weight b * (row.point (localEndpoints c).1 * row.point (localEndpoints c).2) *
          slopeNormalFormula a (localSlopeEdge c) row.component
      else 0
  | .motion b i q =>
      if i ∈ row.support then row.weight b * row.point i *
        (oldLinearValueFormula a s row.support row.point (Fin.natAdd m b) (basisFormula q) row.component -
          oldLinearValueFormula a s row.support row.point (Fin.castAdd 2 i) (basisFormula q) row.component)
      else 0
  | .extra b i u =>
      if i.val ∈ row.support then row.weight b * row.point i.val *
        oldLinearValueFormula a s row.support row.point (Fin.natAdd m b)
          (shiftLinearFormula u (slopeNormalFormula a (crossEdge i.val b))) row.component
      else 0
  | .remaining b u q => row.weight b *
      oldRemainingValueFormula a s row.support row.point (Fin.natAdd m b) u (basisFormula q) row.component

variable {K : Type*} [Field K]

/-- A formula row denotes the supplied coordinates and weights of one actual probe. -/
structure B11ProbeFormula.Matches (x : σ → K) (row : B11ProbeFormula σ m)
    (p : B11Probe K m) : Prop where
  point : ∀ i ∈ row.support, Formula.Matches x (row.point i) (p.point i)
  supported : ∀ i ∉ row.support, p.point i = 0
  weight : ∀ b, Formula.Matches x (row.weight b) (p.weight b)
  component : row.component = p.component

private theorem sum_on_support (S : Finset (Fin m)) (f : Fin m → K)
    (h : ∀ i ∉ S, f i = 0) : (∑ i ∈ S, f i) = ∑ i, f i :=
  Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => h i hi)

private theorem matches_sum_of_support (x : σ → K) (S : Finset (Fin m))
    (f : Fin m → Formula σ) (g : Fin m → K)
    (hm : ∀ i ∈ S, Formula.Matches x (f i) (g i)) (hz : ∀ i ∉ S, g i = 0) :
    Formula.Matches x (orderedSupportSum S f) (∑ i, g i) := by
  let l := (List.finRange m).filter (fun i => decide (i ∈ S))
  have hmem (i : Fin m) : i ∈ l ↔ i ∈ S := by simp [l, List.mem_finRange]
  have hn : l.Nodup := List.Nodup.filter _ (List.nodup_finRange m)
  have hl : l.toFinset = S := by
    ext i
    simpa only [List.mem_toFinset] using hmem i
  have hs := Formula.Matches.sumList l (fun i hi => hm i ((hmem i).mp hi))
  have he := ((List.toFinset_toList hn).map g).sum_eq
  rw [Finset.sum_map_toList, hl, sum_on_support S g hz] at he
  exact he.symm ▸ hs

private theorem zeroFormula_matches (x : σ → K) : Formula.Matches x (0 : Formula σ) (0 : K) := by
  simpa using Formula.Matches.ofNat x 0

private theorem oneFormula_matches (x : σ → K) : Formula.Matches x (1 : Formula σ) (1 : K) := by
  simpa using Formula.Matches.ofNat x 1

private theorem basisFormula_matches (x : σ → K) (q r : Fin 3) :
    Formula.Matches x (basisFormula q r) (normalBasis q r) := by
  by_cases h : r = q
  · simpa [basisFormula, normalBasis, h] using oneFormula_matches x
  · simpa [basisFormula, normalBasis, h] using zeroFormula_matches x

private theorem shiftLinearFormula_matches (x : σ → K) (u : Fin 2)
    (a : Fin 2 → Formula σ) (v : Fin 2 → K) (h : ∀ i, Formula.Matches x (a i) (v i)) (r : Fin 3) :
    Formula.Matches x (shiftLinearFormula u a r) (shiftLinear u v r) := by
  fin_cases u <;> fin_cases r
  all_goals first | exact h 0 | exact h 1 | exact zeroFormula_matches x

private theorem shiftQuadraticFormula_matches (x : σ → K) (u : Fin 2)
    (a : Fin 3 → Formula σ) (v : Fin 3 → K) (h : ∀ i, Formula.Matches x (a i) (v i)) (r : Fin 4) :
    Formula.Matches x (shiftQuadraticFormula u a r) (shiftQuadratic u v r) := by
  fin_cases u <;> fin_cases r
  all_goals first | exact h 0 | exact h 1 | exact h 2 | exact zeroFormula_matches x

private theorem slopeNormalFormula_matches (Q : Parameters K (m + 2)) (x : σ → K)
    (a : PrimitiveIndex (m + 2) → Formula σ) (ha : ∀ i, Formula.Matches x (a i) (primitiveValue Q i))
    (e : Edge (m + 2)) (r : Fin 2) :
    Formula.Matches x (slopeNormalFormula a e r) (![Q.edgeSlope e 0, -1] r) := by
  fin_cases r
  · exact ha (.edgeSlope e 0)
  · exact (oneFormula_matches x).neg

variable (Q : Parameters K (m + 2)) (x : σ → K)
variable (a : PrimitiveIndex (m + 2) → Formula σ)
variable (ha : ∀ i, Formula.Matches x (a i) (primitiveValue Q i))
variable {row : B11ProbeFormula σ m} {p : B11Probe K m}

include ha in
private theorem oldLinearValueFormula_matches (hrow : row.Matches x p)
    (c : Fin (m + 2)) (q : Fin 3 → Formula σ) (v : Fin 3 → K)
    (hq : ∀ j, Formula.Matches x (q j) (v j)) (r : Fin 2) :
    Formula.Matches x (oldLinearValueFormula a Q.single row.support row.point c q r)
      (oldLinearValue Q c v p.point r) := by
  unfold oldLinearValueFormula oldLinearValue
  refine matches_sum_of_support x row.support _ _ ?_ ?_
  · intro i hi
    exact (mixedLinearFormula_matches a x Q ha hq c (Fin.castAdd 2 i) r).mul (hrow.point i hi)
  · intro i hi
    simp [hrow.supported i hi]

include ha in
private theorem oldPureValueFormula_matches (hrow : row.Matches x p)
    (q : Fin 4 → Formula σ) (v : Fin 4 → K)
    (hq : ∀ j, Formula.Matches x (q j) (v j)) (r : Fin 2) :
    Formula.Matches x (oldPureValueFormula a Q.single row.support row.point q r)
      (oldPureValue Q v p.point r) := by
  unfold oldPureValueFormula oldPureValue
  refine matches_sum_of_support x row.support _ _ ?_ ?_
  · intro i hi
    refine matches_sum_of_support x row.support _ _ ?_ ?_
    · intro j hj
      have hcoeff := upperCoefficientFormula_matches x
        (fun i r => pureDiagonalFormula_matches a x Q ha hq i r)
        (fun e r => pureOffDiagonalFormula_matches a x Q ha hq e r)
        (Fin.castAdd 2 i) (Fin.castAdd 2 j) r
      exact (hcoeff.mul (hrow.point i hi)).mul (hrow.point j hj)
    · intro j hj
      simp [hrow.supported j hj]
  · intro i hi
    simp [hrow.supported i hi]

include ha in
private theorem oldRemainingValueFormula_matches (hrow : row.Matches x p)
    (c : Fin (m + 2)) (u : Fin 2) (q : Fin 3 → Formula σ) (v : Fin 3 → K)
    (hq : ∀ j, Formula.Matches x (q j) (v j)) (r : Fin 2) :
    Formula.Matches x (oldRemainingValueFormula a Q.single row.support row.point c u q r)
      (oldRemainingValue Q c u v p.point r) := by
  unfold oldRemainingValueFormula oldRemainingValue
  apply Formula.Matches.add
  · exact oldPureValueFormula_matches Q x a ha hrow _ _ (shiftQuadraticFormula_matches x u q v hq) r
  · refine matches_sum_of_support x row.support _ _ ?_ ?_
    · intro i hi
      refine (hrow.point i hi).mul (oldLinearValueFormula_matches Q x a ha hrow c _ _ ?_ r)
      exact shiftLinearFormula_matches x u _ _ (mixedLinearFormula_matches a x Q ha hq c (Fin.castAdd 2 i))
    · intro i hi
      simp [hrow.supported i hi]

include ha in
/-- The supported rational formula is admissible and evaluates to the actual B.11 entry. -/
theorem b11EntryFormula_matches (hrow : row.Matches x p) (c : B7Column m) :
    Formula.Matches x (b11EntryFormula a Q.single row c) (probeEntry (actualB7Data Q) p c) := by
  rw [probeEntry, b7Value_actual_eq_oldValue, ← hrow.component]
  cases c with
  | localColumn b c =>
    by_cases hs : (localEndpoints c).1 ∈ row.support ∧ (localEndpoints c).2 ∈ row.support
    · simp only [b11EntryFormula, hs, b7OldValue, localValue]
      exact ((hrow.weight b).mul ((hrow.point _ hs.1).mul (hrow.point _ hs.2))).mul
        (slopeNormalFormula_matches Q x a ha (localSlopeEdge c) row.component)
    · have hz : p.point (localEndpoints c).1 = 0 ∨ p.point (localEndpoints c).2 = 0 := by
        by_cases h₁ : (localEndpoints c).1 ∈ row.support
        · exact Or.inr (hrow.supported _ (fun h₂ => hs ⟨h₁, h₂⟩))
        · exact Or.inl (hrow.supported _ h₁)
      rcases hz with h | h <;>
        simpa [b11EntryFormula, hs, b7OldValue, localValue, h] using zeroFormula_matches x
  | motion b i q =>
    by_cases hi : i ∈ row.support
    · simp only [b11EntryFormula, hi, b7OldValue]
      exact ((hrow.weight b).mul (hrow.point i hi)).mul
        ((oldLinearValueFormula_matches Q x a ha hrow (Fin.natAdd m b) _ _ (basisFormula_matches x q) _).sub
          (oldLinearValueFormula_matches Q x a ha hrow (Fin.castAdd 2 i) _ _ (basisFormula_matches x q) _))
    · simpa [b11EntryFormula, hi, b7OldValue, hrow.supported i hi] using zeroFormula_matches x
  | extra b i u =>
    by_cases hi : i.val ∈ row.support
    · simp only [b11EntryFormula, hi, b7OldValue]
      refine ((hrow.weight b).mul (hrow.point _ hi)).mul
        (oldLinearValueFormula_matches Q x a ha hrow (Fin.natAdd m b) _ _ ?_ _)
      exact shiftLinearFormula_matches x u _ _ (slopeNormalFormula_matches Q x a ha (crossEdge i.val b))
    · simpa [b11EntryFormula, hi, b7OldValue, hrow.supported i.val hi] using zeroFormula_matches x
  | remaining b u q =>
    exact (hrow.weight b).mul (oldRemainingValueFormula_matches Q x a ha hrow
      (Fin.natAdd m b) u _ _ (basisFormula_matches x q) row.component)

/-- The evaluated row and column selection used in the supported matrices. -/
def b11FormulaMatrix {ι κ : Type*} (s : Edge (m + 2) → Bool)
    (rows : ι → B11ProbeFormula σ m) (cols : κ → B7Column m) : Matrix ι κ (Formula σ) :=
  fun i j => b11EntryFormula a s (rows i) (cols j)

include ha in
/-- Evaluating the formula matrix gives the actual selected B.11 entries. -/
theorem b11FormulaMatrix_spec {ι κ : Type*} (rows : ι → B11ProbeFormula σ m)
    (probes : ι → B11Probe K m) (cols : κ → B7Column m)
    (hrows : ∀ i, (rows i).Matches x (probes i)) :
    EntriesAdmissible x (b11FormulaMatrix a Q.single rows cols) ∧
      evalMatrix x (b11FormulaMatrix a Q.single rows cols) =
        Matrix.of (fun i j => probeEntry (actualB7Data Q) (probes i) (cols j)) := by
  refine ⟨fun i j => (b11EntryFormula_matches Q x a ha (hrows i) (cols j)).1, ?_⟩
  ext i j
  exact (b11EntryFormula_matches Q x a ha (hrows i) (cols j)).2

/-- The denominator-cleared integer polynomial of a selected B.11 square block. -/
def b11Certificate {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Edge (m + 2) → Bool)
    (rows : ι → B11ProbeFormula σ m) (cols : ι → B7Column m) : MvPolynomial σ ℤ :=
  matrixCertificate (b11FormulaMatrix a s rows cols)

include ha in
/-- On valid cone and sample data, the integer polynomial detects the actual block determinant. -/
theorem eval_b11Certificate_ne_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rows : ι → B11ProbeFormula σ m) (probes : ι → B11Probe K m) (cols : ι → B7Column m)
    (hrows : ∀ i, (rows i).Matches x (probes i)) :
    evalPolynomial x (b11Certificate a Q.single rows cols) ≠ 0 ↔
      (Matrix.of (fun i j => probeEntry (actualB7Data Q) (probes i) (cols j))).det ≠ 0 := by
  obtain ⟨hadm, heval⟩ := b11FormulaMatrix_spec Q x a ha rows probes cols hrows
  rw [b11Certificate, eval_matrixCertificate_ne_zero_iff, heval]
  exact and_iff_right hadm

end IdealGeneration.CubicSupported.B5
