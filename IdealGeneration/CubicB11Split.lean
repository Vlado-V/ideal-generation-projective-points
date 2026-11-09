module

public import IdealGeneration.CubicB11Formula
public import IdealGeneration.CubicPrimitiveSplit

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Splitting the B.11 polynomial into old cone parameters and new parameters with samples. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open RationalChart CubicRationalFormula

variable {K : Type*} [Field K] {m : ℕ} {Sample : Type*}

/-- Samples and the complement of the chosen old prefix form the new variables. -/
abbrev B11SplitAlong {n N : ℕ} (e : PrimitiveIndex n ↪ PrimitiveIndex N) (Sample : Type*) :=
  (NewPrimitiveAlong e ⊕ Sample) ⊕ PrimitiveIndex n

/-- The joint assignment of primitive data and sample values along a prefix. -/
def b11AssignmentAlong {n : ℕ} (e : PrimitiveIndex n ↪ PrimitiveIndex (m + 2))
    (Q : Parameters K (m + 2)) (old : PrimitiveIndex n → K) (samples : Sample → K) :
    B11SplitAlong e Sample → K :=
  Sum.elim (Sum.elim (fun i => primitiveValue Q i.val) samples) old

/-- Read a primitive parameter through its old or new variable. -/
def b11PrimitiveAlong {n : ℕ} (e : PrimitiveIndex n ↪ PrimitiveIndex (m + 2))
    (i : PrimitiveIndex (m + 2)) : Formula (B11SplitAlong e Sample) :=
  .var (Sum.map Sum.inl id ((primitiveSplitEquiv e).symm i))

/-- The split formula agrees with the actual primitive if the fixed old assignment does. -/
theorem b11PrimitiveAlong_matches {n : ℕ} (e : PrimitiveIndex n ↪ PrimitiveIndex (m + 2))
    (Q : Parameters K (m + 2)) (old : PrimitiveIndex n → K) (samples : Sample → K)
    (hold : ∀ i, old i = primitiveValue Q (e i)) (i : PrimitiveIndex (m + 2)) :
    Formula.Matches (b11AssignmentAlong e Q old samples) (b11PrimitiveAlong e i) (primitiveValue Q i) := by
  obtain ⟨j, rfl⟩ := (primitiveSplitEquiv e).surjective i
  unfold b11PrimitiveAlong
  rw [Equiv.symm_apply_apply]
  rcases j with j | j
  · exact Formula.Matches.var (b11AssignmentAlong e Q old samples) (.inl (.inl j))
  · have hm : Formula.Matches (b11AssignmentAlong e Q old samples) (.var (.inr j)) (old j) :=
      Formula.Matches.var _ _
    rw [hold] at hm
    exact hm

/-- Samples belong to the freely chosen side of the two-variable extension. -/
abbrev B11SplitIndex (m : ℕ) (Sample : Type*) := B11SplitAlong (oldPrimitiveIndex m) Sample

/-- The joint actual cone and sample assignment for the two-variable extension. -/
def b11SplitAssignment (Q : Parameters K (m + 2)) (old : PrimitiveIndex m → K)
    (samples : Sample → K) : B11SplitIndex m Sample → K :=
  b11AssignmentAlong (oldPrimitiveIndex m) Q old samples

/-- The primitive variable in the two-variable extension. -/
def b11SplitPrimitive (m : ℕ) (i : PrimitiveIndex (m + 2)) : Formula (B11SplitIndex m Sample) :=
  b11PrimitiveAlong (oldPrimitiveIndex m) i

/-- The primitive formulas match every parameter of a compatible enlarged cone. -/
theorem b11SplitPrimitive_matches (Q : Parameters K (m + 2)) (old : PrimitiveIndex m → K)
    (samples : Sample → K) (hold : ∀ i, old i = primitiveValue Q (oldPrimitiveIndex m i))
    (i : PrimitiveIndex (m + 2)) :
    Formula.Matches (b11SplitAssignment Q old samples) (b11SplitPrimitive m i) (primitiveValue Q i) :=
  b11PrimitiveAlong_matches (oldPrimitiveIndex m) Q old samples hold i

/-- Sample coordinates and weights are independent new variables. -/
def b11SampleVariable (m : ℕ) (i : Sample) : Formula (B11SplitIndex m Sample) := .var (.inl (.inr i))

@[simp] theorem b11SampleVariable_matches (Q : Parameters K (m + 2)) (old : PrimitiveIndex m → K)
    (samples : Sample → K) (i : Sample) :
    Formula.Matches (b11SplitAssignment Q old samples) (b11SampleVariable m i) (samples i) :=
  Formula.Matches.var _ _

/-- One supported sample row with chosen labels for its coordinates and weights. -/
def b11SampleProbe (S : Finset (Fin m)) (pointLabel : Fin m → Sample) (weightLabel : Fin 2 → Sample)
    (r : Fin 2) : B11ProbeFormula (B11SplitIndex m Sample) m where
  support := S
  point := b11SampleVariable m ∘ pointLabel
  weight := b11SampleVariable m ∘ weightLabel
  component := r

/-- Reading the sample variables gives the supported sample's actual probe. -/
theorem b11SampleProbe_matches (Q : Parameters K (m + 2)) (old : PrimitiveIndex m → K)
    (samples : Sample → K) (S : Finset (Fin m)) (pointLabel : Fin m → Sample)
    (weightLabel : Fin 2 → Sample) (r : Fin 2) (p : B11Probe K m)
    (hp : ∀ i ∈ S, samples (pointLabel i) = p.point i)
    (hs : ∀ i ∉ S, p.point i = 0) (hw : ∀ b, samples (weightLabel b) = p.weight b)
    (hr : r = p.component) :
    (b11SampleProbe S pointLabel weightLabel r).Matches (b11SplitAssignment Q old samples) p := by
  refine ⟨?_, hs, ?_, hr⟩
  · intro i hi
    exact hp i hi ▸ b11SampleVariable_matches Q old samples (pointLabel i)
  · intro b
    exact hw b ▸ b11SampleVariable_matches Q old samples (weightLabel b)

variable {σ : Type*}

/-- The probe on a vertex or an edge with a symbolic edge parameter. -/
def b11FaceProbeFormula (F : Face m) (η : Formula σ) (b r : Fin 2) : B11ProbeFormula σ m where
  support := faceVertices F
  point := match F with
    | .inl _ => fun _ => 1
    | .inr e => fun i => if i = e.val.1 then 1 else η
  weight := fun d => if d = b then 1 else 0
  component := r

/-- Face probes use exactly the normalized edge coordinate and the pure direction. -/
theorem b11FaceProbeFormula_matches (x : σ → K) (F : Face m) (η : Formula σ) (t : K)
    (hη : Formula.Matches x η t) (b r : Fin 2) :
    (b11FaceProbeFormula F η b r).Matches x ⟨faceProbe F t, pureDirection b, r⟩ := by
  have h₀ : Formula.Matches x (0 : Formula σ) (0 : K) := by simpa using Formula.Matches.ofNat x 0
  have h₁ : Formula.Matches x (1 : Formula σ) (1 : K) := by simpa using Formula.Matches.ofNat x 1
  refine ⟨?_, fun _ hi => faceProbe_eq_zero_of_not_mem F t hi, ?_, rfl⟩
  · intro i hi
    rcases F with v | e
    · have he : i = v := by simpa [b11FaceProbeFormula, faceVertices] using hi
      subst i
      simpa [b11FaceProbeFormula, faceProbe, vertexSupport] using h₁
    · have he : i = e.val.1 ∨ i = e.val.2 := by
        simpa [b11FaceProbeFormula, faceVertices] using hi
      rcases he with h | h
      · simp [b11FaceProbeFormula, faceProbe, edgeSupport, vertexSupport, h, ne_of_lt e.property, h₁]
      · simp [b11FaceProbeFormula, faceProbe, edgeSupport, vertexSupport, h, (ne_of_lt e.property).symm, hη]
  · intro d
    by_cases h : d = b
    · simpa [b11FaceProbeFormula, pureDirection, h] using h₁
    · simpa [b11FaceProbeFormula, pureDirection, h] using h₀

/-- The selected block polynomial in the old and new variables of B.6. -/
def b11SplitCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (single : Edge (m + 2) → Bool) (rows : ι → B11ProbeFormula (B11SplitIndex m Sample) m)
    (cols : ι → B7Column m) : MvPolynomial (B11SplitIndex m Sample) ℤ :=
  b11Certificate (b11SplitPrimitive m) single rows cols

/-- On compatible cone and sample data, the split polynomial detects the actual block. -/
theorem eval_b11SplitCertificate_ne_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Parameters K m} {Q : Parameters K (m + 2)} (h : Compatible P Q) (samples : Sample → K)
    (rows : ι → B11ProbeFormula (B11SplitIndex m Sample) m) (probes : ι → B11Probe K m)
    (cols : ι → B7Column m)
    (hrows : ∀ i, (rows i).Matches (b11SplitAssignment Q (primitiveValue P) samples) (probes i)) :
    evalPolynomial (b11SplitAssignment Q (primitiveValue P) samples) (b11SplitCertificate Q.single rows cols) ≠ 0 ↔
      (Matrix.of (fun i j => probeEntry (actualB7Data Q) (probes i) (cols j))).det ≠ 0 :=
  eval_b11Certificate_ne_zero_iff Q _ _
    (b11SplitPrimitive_matches Q (primitiveValue P) samples (fun i => (primitiveValue_oldPrimitiveIndex h i).symm))
    rows probes cols hrows

end IdealGeneration.CubicSupported.B5
