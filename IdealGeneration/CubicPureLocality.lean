module

public import IdealGeneration.CubicMixedLocality
public import IdealGeneration.QuadraticTraceRestriction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Locality of the pure cubic lifts and their trace evaluations. -/

namespace IdealGeneration.CubicPureLocality

open CubicSupported CubicMixedLocality CubicNormalExpansion
open QuadraticTraceRestriction MvPolynomial

variable {K : Type*} [Field K] {n m : ℕ}
variable {P : Parameters K n} {L : Parameters K m} {ι : Fin n ↪ Fin m} {hι : StrictMono ι}

/-- The diagonal of a pure lift uses only the corresponding vertex data. -/
theorem pureCubic_diagonal_eq (C₀ : Fin 4 → K) {i : Fin n} (h : AgreesAt P L ι hι i) :
    (P.pureCubic C₀).val.2.2.1 i = (L.pureCubic C₀).val.2.2.1 (ι i) := by
  change P.diagonalLift C₀ 0 i = L.diagonalLift C₀ 0 (ι i)
  simp [Parameters.diagonalLift, Parameters.diagonalRhs, h.vertexSlope_eq, h.vertexHeight_eq]

/-- The pure edge solve uses that edge's parameters and the two endpoint diagonals. -/
theorem pureCubic_offDiagonal_eq (C₀ : Fin 4 → K) (e : Edge n)
    (hleft : AgreesAt P L ι hι e.val.1) (hright : AgreesAt P L ι hι e.val.2) :
    (P.pureCubic C₀).val.2.2.2 e = (L.pureCubic C₀).val.2.2.2 (edgeImage ι hι e) := by
  change P.offDiagonalLift C₀ 0 0 e = L.offDiagonalLift C₀ 0 0 (edgeImage ι hι e)
  obtain ⟨hsingle, hlam, hslope, hheight⟩ := hleft.edge_eq e (Or.inl rfl)
  have hD₁ : P.diagonalLift C₀ 0 e.val.1 = L.diagonalLift C₀ 0 (ι e.val.1) :=
    pureCubic_diagonal_eq C₀ hleft
  have hD₂ : P.diagonalLift C₀ 0 e.val.2 = L.diagonalLift C₀ 0 (ι e.val.2) :=
    pureCubic_diagonal_eq C₀ hright
  have hRhs (d : Fin 2) : P.edgeRhs C₀ 0 e d = L.edgeRhs C₀ 0 (edgeImage ι hι e) d := by
    simp only [Parameters.edgeRhs, edgeImage_fst, edgeImage_snd, hlam, hslope, hheight,
      Pi.zero_apply, hD₁, hD₂]
  by_cases hs : P.single e = true
  · have hs' : L.single (edgeImage ι hι e) = true := hsingle.symm.trans hs
    simp [Parameters.offDiagonalLift, hs, hs', hRhs]
  · have hs' : ¬ L.single (edgeImage ι hι e) = true := fun he => hs (hsingle.trans he)
    simp [Parameters.offDiagonalLift, hs, hs', hslope, hRhs]

/-- The upper-triangular pure coefficient array restricts to the embedded graph. -/
theorem pureCubic_upperCoefficient_eq (C₀ : Fin 4 → K) (i j : Fin n) (k : Fin 2)
    (hi : AgreesAt P L ι hι i) (hj : AgreesAt P L ι hι j) :
    upperCoefficient (P.pureCubic C₀).val.2.2.1 (P.pureCubic C₀).val.2.2.2 i j k =
      upperCoefficient (L.pureCubic C₀).val.2.2.1 (L.pureCubic C₀).val.2.2.2 (ι i) (ι j) k := by
  by_cases hij : i < j
  · simp only [upperCoefficient, dite_eq_left hij, dite_eq_left (hι hij)]
    exact congrFun (pureCubic_offDiagonal_eq C₀ ⟨(i, j), hij⟩ hi hj) k
  · by_cases heq : i = j
    · subst j
      simp only [upperCoefficient_diagonal]
      exact congrFun (pureCubic_diagonal_eq C₀ hi) k
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm heq)
      have hij' : ¬ ι i < ι j := not_lt_of_ge (hι hji).le
      have heq' : ι i ≠ ι j := fun h => heq (ι.injective h)
      simp [upperCoefficient, hij, hij', heq, heq']

/-- Zero extension restricts both sums of a trace quadratic to the embedded coordinates. -/
theorem traceQuadratic_extendPoint (ι : Fin n ↪ Fin m)
    (A : Fin m → Fin m → K) (y : Fin n → K) :
    traceQuadratic A (extendPoint K ι y) = traceQuadratic (fun i j => A (ι i) (ι j)) y := by
  let z := extendPoint K ι y
  have hz (i : Fin m) (hi : i ∉ Set.range ι) : z i = 0 := extendPoint_off K ι y hi
  change (∑ i : Fin m, ∑ j : Fin m, A i j * z i * z j) =
    ∑ i : Fin n, ∑ j : Fin n, A (ι i) (ι j) * y i * y j
  rw [sum_over_embedding ι (fun i => ∑ j : Fin m, A i j * z i * z j)
    (fun i hi => by simp [hz i hi])]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_over_embedding ι (fun j => A (ι i) j * z (ι i) * z j)
    (fun j hj => by simp [hz j hj])]
  simp [z]

private theorem eval_traceA (u : Coefficients K m) (k : Fin 2) (y : Fin m → K) :
    eval y (traceA u k) = traceQuadratic (fun i j => upperCoefficient u.2.2.1 u.2.2.2 i j k) y := by
  simp [traceA, traceQuadratic, map_sum]

/-- Evaluation of the actual pure trace coefficient commutes with zero extension. -/
theorem eval_traceA_pureCubic_extendPoint (h : ∀ i, AgreesAt P L ι hι i)
    (C₀ : Fin 4 → K) (k : Fin 2) (y : Fin n → K) :
    eval (extendPoint K ι y) (traceA (L.pureCubic C₀).val k) =
      eval y (traceA (P.pureCubic C₀).val k) := by
  rw [eval_traceA, eval_traceA, traceQuadratic_extendPoint]
  congr 1
  funext i j
  exact (pureCubic_upperCoefficient_eq C₀ i j k (h i) (h j)).symm

/-- Extend a trace embedding while sending the appended pair to the appended pair. -/
def appendTwoEmbedding (ι : Fin n ↪ Fin m) : Fin (n + 2) ↪ Fin (m + 2) :=
  ((finSumFinEquiv (m := n) (n := 2)).symm.toEmbedding.trans
    (ι.sumMap (Function.Embedding.refl (Fin 2)))).trans
    (finSumFinEquiv (m := m) (n := 2)).toEmbedding

@[simp] theorem appendTwoEmbedding_old (ι : Fin n ↪ Fin m) (i : Fin n) :
    appendTwoEmbedding ι (Fin.castAdd 2 i) = Fin.castAdd 2 (ι i) := by
  simp [appendTwoEmbedding]

@[simp] theorem appendTwoEmbedding_new (ι : Fin n ↪ Fin m) (j : Fin 2) :
    appendTwoEmbedding ι (Fin.natAdd n j) = Fin.natAdd m j := by
  simp [appendTwoEmbedding]

theorem appendTwoEmbedding_strictMono (ι : Fin n ↪ Fin m) (hι : StrictMono ι) :
    StrictMono (appendTwoEmbedding ι) := by
  intro i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · refine Fin.addCases (fun b hab => ?_) (fun b _ => ?_) j
    · simp only [appendTwoEmbedding_old]
      exact hι (show a < b from hab)
    · rw [appendTwoEmbedding_old, appendTwoEmbedding_new]
      change (ι a).val < m + b.val
      have := (ι a).isLt
      omega
  · refine Fin.addCases (fun b hab => ?_) (fun b hab => ?_) j
    · exfalso
      change n + a.val < b.val at hab
      have := b.isLt
      omega
    · simp only [appendTwoEmbedding_new]
      change m + a.val < m + b.val
      change n + a.val < n + b.val at hab
      omega

/-- Zero extension preserves the two appended coordinates and extends the old coordinates by zero. -/
theorem extendPoint_appendTwoEmbedding_addCases (ι : Fin n ↪ Fin m) (y : Fin n → K) (c : Fin 2 → K) :
    extendPoint K (appendTwoEmbedding ι) (Fin.addCases y c) =
      Fin.addCases (extendPoint K ι y) c := by
  classical
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · by_cases ha : a ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := ha
      simpa only [appendTwoEmbedding_old, Fin.addCases_left, extendPoint_embedded] using
        (extendPoint_embedded K (appendTwoEmbedding ι) (Fin.addCases y c) (Fin.castAdd 2 j))
    · have hoff : Fin.castAdd 2 a ∉ Set.range (appendTwoEmbedding ι) := by
        rintro ⟨j, hj⟩
        revert hj
        refine Fin.addCases (fun r hr => ?_) (fun s hs => ?_) j
        · rw [appendTwoEmbedding_old] at hr
          have hv := congrArg Fin.val hr
          exact ha ⟨r, Fin.ext hv⟩
        · rw [appendTwoEmbedding_new] at hs
          have hv := congrArg Fin.val hs
          change m + s.val = a.val at hv
          have := a.isLt
          omega
      simp only [extendPoint_off K (appendTwoEmbedding ι) (Fin.addCases y c) hoff,
        Fin.addCases_left, extendPoint_off K ι y ha]
  · simpa only [appendTwoEmbedding_new, Fin.addCases_right] using
      (extendPoint_embedded K (appendTwoEmbedding ι) (Fin.addCases y c) (Fin.natAdd n b))

end IdealGeneration.CubicPureLocality
