module

public import IdealGeneration.ConeSplitting
public import IdealGeneration.ProjectiveTransport
public import IdealGeneration.RepresentativeGeneric

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Normalized chart witnesses from cone configurations

The coordinate cone multiplication is canonically the multiplication of its
ordered representatives. A projective coordinate change and nonzero rescaling
therefore preserve the cone calculation in a normalized affine chart.
-/

noncomputable section
namespace IdealGeneration
namespace ConeConfiguration

variable {K : Type*} [Field K] {c m p q d : ℕ}
  (C : ConeConfiguration K c m p q)

/-- Identify the source tuples for cone and representative multiplication. -/
def representativeSourceEquiv (d : ℕ) :
    (Fin (c + m) → C.unionPiece d) ≃ₗ[K]
      (Fin (c + m) → representativePiece K C.representatives d) :=
  LinearEquiv.piCongrRight (fun _ => C.representativeEquiv d)

/-- The canonical source and target identifications commute with coordinate
multiplication. -/
theorem representativeSourceEquiv_multiplication (d : ℕ)
    (f : Fin (c + m) → C.unionPiece d) :
    representativeMultiplication K C.representatives d
        (C.representativeSourceEquiv d f) =
      C.representativeEquiv (d + 1) (C.multiplication d f) :=
  (C.representativeEquiv_multiplication d f).symm

/-- Cone and representative multiplication have the same injectivity. -/
theorem multiplication_representative_injective_iff (d : ℕ) :
    Function.Injective (C.multiplication d) ↔
      Function.Injective (representativeMultiplication K C.representatives d) := by
  constructor
  · intro h f g hfg
    obtain ⟨f, rfl⟩ := (C.representativeSourceEquiv d).surjective f
    obtain ⟨g, rfl⟩ := (C.representativeSourceEquiv d).surjective g
    apply congrArg (C.representativeSourceEquiv d)
    apply h
    apply (C.representativeEquiv (d + 1)).injective
    simpa only [← C.representativeSourceEquiv_multiplication] using hfg
  · intro h f g hfg
    apply (C.representativeSourceEquiv d).injective
    apply h
    rw [C.representativeSourceEquiv_multiplication,
      C.representativeSourceEquiv_multiplication, hfg]

/-- Cone and representative multiplication have the same surjectivity. -/
theorem multiplication_representative_surjective_iff (d : ℕ) :
    Function.Surjective (C.multiplication d) ↔
      Function.Surjective (representativeMultiplication K C.representatives d) := by
  constructor
  · intro h f
    obtain ⟨f, rfl⟩ := (C.representativeEquiv (d + 1)).surjective f
    obtain ⟨g, hg⟩ := h f
    exact ⟨C.representativeSourceEquiv d g, by
      rw [C.representativeSourceEquiv_multiplication, hg]⟩
  · intro h f
    obtain ⟨g, hg⟩ := h (C.representativeEquiv (d + 1) f)
    obtain ⟨g, rfl⟩ := (C.representativeSourceEquiv d).surjective g
    refine ⟨g, (C.representativeEquiv (d + 1)).injective ?_⟩
    simpa only [← C.representativeSourceEquiv_multiplication] using hg

/-- Maximal rank of the cone map is maximal rank of its actual representative
multiplication. -/
theorem multiplication_representative_maximalRank_iff (d : ℕ) :
    HasMaximalRank (C.multiplication d) ↔
      HasMaximalRank (representativeMultiplication K C.representatives d) := by
  unfold HasMaximalRank
  rw [C.multiplication_representative_injective_iff,
    C.multiplication_representative_surjective_iff]

/-- A nonzero cone configuration has normalized chart representatives with
the same equation dimensions, injectivity, and surjectivity in every degree. -/
theorem exists_chart_transport [Infinite K] (hN : 0 < c + m)
    (hz : ∀ i, C.representatives i ≠ 0) :
    ∃ a : PointCoordinates K (c + m - 1) (p + q),
      (∀ j, Module.finrank K (pointDegreePiece K a j) =
        Module.finrank K (C.unionPiece j)) ∧
      (∀ j, Function.Injective (C.multiplication j) ↔
        Function.Injective (pointMultiplication a j)) ∧
      (∀ j, Function.Surjective (C.multiplication j) ↔
        Function.Surjective (pointMultiplication a j)) := by
  obtain ⟨a, hdim, hinj, hsurj⟩ :=
    IdealGeneration.exists_chart_transport_of_pos hN C.representatives hz
  refine ⟨a, ?_, ?_, ?_⟩
  · intro j
    exact ((C.representativeEquiv j).finrank_eq.trans (hdim j)).symm
  · intro j
    exact (C.multiplication_representative_injective_iff j).trans (hinj j)
  · intro j
    exact (C.multiplication_representative_surjective_iff j).trans (hsurj j)

/-- Nonzero normal directions and nonzero trace points supply the nonzero
representatives needed for chart transport. -/
theorem exists_chart_transport_of_nonzero [Infinite K] (hN : 0 < c + m)
    (hnormal : ∀ i, C.normal i ≠ 0) (htrace : ∀ i, C.trace i ≠ 0) :
    ∃ a : PointCoordinates K (c + m - 1) (p + q),
      (∀ j, Module.finrank K (pointDegreePiece K a j) =
        Module.finrank K (C.unionPiece j)) ∧
      (∀ j, Function.Injective (C.multiplication j) ↔
        Function.Injective (pointMultiplication a j)) ∧
      (∀ j, Function.Surjective (C.multiplication j) ↔
        Function.Surjective (pointMultiplication a j)) :=
  C.exists_chart_transport hN (C.representatives_ne_zero hnormal htrace)

/-- A maximal-rank cone witness yields a maximal-rank chart witness while
preserving all equation dimensions. -/
theorem exists_chart_maximalRank [Infinite K] (hN : 0 < c + m)
    (hz : ∀ i, C.representatives i ≠ 0) (h : HasMaximalRank (C.multiplication d)) :
    ∃ a : PointCoordinates K (c + m - 1) (p + q),
      (∀ j, Module.finrank K (pointDegreePiece K a j) =
        Module.finrank K (C.unionPiece j)) ∧
      HasMaximalRank (pointMultiplication a d) := by
  obtain ⟨a, hdim, hinj, hsurj⟩ := C.exists_chart_transport hN hz
  exact ⟨a, hdim, h.elim (fun hi => Or.inl ((hinj d).mp hi))
    (fun hs => Or.inr ((hsurj d).mp hs))⟩

/-- With bijective trace multiplication, a maximal-rank middle map gives a
chart witness with the degree-piece dimensions prescribed by the cone split. -/
theorem exists_chart_maximalRank_of_middle [Infinite K] (hN : 0 < c + m)
    (hz : ∀ i, C.representatives i ≠ 0)
    (htrace : Function.Bijective (C.traceMultiplication d))
    (hmiddle : HasMaximalRank (C.middleMultiplication d)) :
    ∃ a : PointCoordinates K (c + m - 1) (p + q),
      (∀ j, Module.finrank K (pointDegreePiece K a j) =
        Module.finrank K (C.tracePiece j) + Module.finrank K (C.residualPiece j)) ∧
      HasMaximalRank (pointMultiplication a d) := by
  obtain ⟨a, hdim, hmult⟩ := C.exists_chart_maximalRank hN hz
    ((C.multiplication_maximalRank_iff d htrace).mpr hmiddle)
  exact ⟨a, fun j => (hdim j).trans (C.finrank_unionPiece j), hmult⟩

/-- An injective cone witness gives the ideal-generation assertion on a
nonempty principal open set of point configurations. -/
theorem idealGenerationAt_of_injective [CharZero K] (hN : 2 ≤ c + m)
    (hz : ∀ i, C.representatives i ≠ 0)
    (hinj : Function.Injective (C.multiplication d)) :
    IdealGenerationAt K (c + m - 1) d (p + q) :=
  IdealGeneration.idealGenerationAt_of_representative_injective_of_two_le
    hN C.representatives hz ((C.multiplication_representative_injective_iff d).mp hinj)

/-- Injectivity of the two actual cone blocks produces a general-points
ideal-generation witness. -/
theorem idealGenerationAt_of_injective_blocks [CharZero K] (hN : 2 ≤ c + m)
    (hz : ∀ i, C.representatives i ≠ 0)
    (htrace : Function.Injective (C.traceMultiplication d))
    (hmiddle : Function.Injective (C.middleMultiplication d)) :
    IdealGenerationAt K (c + m - 1) d (p + q) :=
  C.idealGenerationAt_of_injective hN hz
    ((C.multiplication_injective_iff d).mpr ⟨htrace, hmiddle⟩)

/-- A scalar-postulated maximal-rank cone witness produces a nonempty open set
of point configurations satisfying the ideal-generation assertion. -/
theorem idealGenerationAt_of_witness [CharZero K] (hN : 2 ≤ c + m)
    (hz : ∀ i, C.representatives i ≠ 0)
    (hscalar : Module.finrank K (C.unionPiece d) + (p + q) =
      Module.finrank K (Forms K (c + m) d))
    (hmax : HasMaximalRank (C.multiplication d)) :
    IdealGenerationAt K (c + m - 1) d (p + q) := by
  apply IdealGeneration.idealGenerationAt_of_representative_witness_of_two_le
    hN C.representatives hz
  · apply (representativeEvaluation_surjective_iff C.representatives d).mpr
    rw [← (C.representativeEquiv d).finrank_eq]
    exact hscalar
  · exact (C.multiplication_representative_maximalRank_iff d).mp hmax

/-- The cone construction yields the general-points assertion when the trace
block is bijective, the middle block has maximal rank, and the split dimension
gives scalar postulation. -/
theorem idealGenerationAt_of_middle [CharZero K] (hN : 2 ≤ c + m)
    (hz : ∀ i, C.representatives i ≠ 0)
    (hscalar : Module.finrank K (C.tracePiece d) +
      Module.finrank K (C.residualPiece d) + (p + q) =
        Module.finrank K (Forms K (c + m) d))
    (htrace : Function.Bijective (C.traceMultiplication d))
    (hmiddle : HasMaximalRank (C.middleMultiplication d)) :
    IdealGenerationAt K (c + m - 1) d (p + q) := by
  apply C.idealGenerationAt_of_witness hN hz
  · rw [C.finrank_unionPiece]
    exact hscalar
  · exact (C.multiplication_maximalRank_iff d htrace).mpr hmiddle

end ConeConfiguration
end IdealGeneration
