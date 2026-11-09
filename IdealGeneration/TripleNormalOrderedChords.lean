module

public import IdealGeneration.TripleNormalChordOpen
public import IdealGeneration.TripleNormalEdgeOrder

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The degree-ordered chord triples admit simultaneous independent normals. -/

namespace IdealGeneration.TripleNormal
open scoped Matrix

variable {K : Type*} [Field K] {I : Type*} {N : ℕ}

/-- Each degree-ordered old-new block followed by the new triangle. -/
def orderedChordTriple (hN : 5 ≤ N) (v : Fin N ↪ I) :
    Option (Fin N) → Fin 3 → Chord I
  | some g => fun k => (.inl (v (EdgeOrder.edgeAt hN g k).1), .inr (EdgeOrder.edgeAt hN g k).2)
  | none => fun k => (.inr (EdgeOrder.triangleAt k).val.1, .inr (EdgeOrder.triangleAt k).val.2)

private theorem ordered_chord_witness [CharZero K] (hN : 5 ≤ N) (v : Fin N ↪ I)
    (t : I → K) (ht : Function.Injective t) (g : Option (Fin N)) :
    ∃ u : Fin 3 → K, (chordMatrix t u (orderedChordTriple hN v g)).det ≠ 0 := by
  rcases g with _ | g
  · let u : Fin 3 → K := ![0, 1, 2]
    refine ⟨u, ?_⟩
    have hm : chordMatrix t u (orderedChordTriple hN v none) =
        Matrix.of ![chordNormal (0 : K) 1, chordNormal 0 2, chordNormal 1 2] := by
      ext i j
      fin_cases i <;> simp [chordMatrix, orderedChordTriple, EdgeOrder.triangleAt, u]
    rw [hm]
    norm_num [Matrix.det_fin_three, chordNormal]
  by_cases hfirst : g.val = 0
  · let a : Fin N := ⟨0, by omega⟩
    let b : Fin N := ⟨1, by omega⟩
    have he : orderedChordTriple hN v (some g) = boundaryChords false (v a) (v b) 0 1 := by
      funext j
      simp only [orderedChordTriple, EdgeOrder.edgeAt_first hN g hfirst]
      fin_cases j <;> rfl
    rw [he]
    exact boundary_chord_witness t false ((ht.comp v.injective).ne (by
      intro h
      have he := congrArg Fin.val h
      change 0 = 1 at he
      omega)) (by decide)
  by_cases hlast : g.val + 1 = N
  · let a : Fin N := ⟨N - 1, by omega⟩
    let b : Fin N := ⟨N - 2, by omega⟩
    have he : orderedChordTriple hN v (some g) = boundaryChords true (v a) (v b) 2 1 := by
      funext j
      simp only [orderedChordTriple, EdgeOrder.edgeAt_last hN g hlast]
      fin_cases j <;> rfl
    rw [he]
    exact boundary_chord_witness t true ((ht.comp v.injective).ne (by
      intro h
      have he := congrArg Fin.val h
      change N - 1 = N - 2 at he
      omega)) (by decide)
  have hpos : 0 < g.val := by omega
  have hlt : g.val + 1 < N := by omega
  let a : Fin 3 → I := fun j => v (EdgeOrder.edgeAt hN g j).1
  have ha : Function.Injective (t ∘ a) := by
    intro i j hij
    by_contra h
    exact (EdgeOrder.middle_disjoint hN g hpos hlt h).1
      (v.injective (ht hij))
  have he : orderedChordTriple hN v (some g) = fun j => (.inl (a j), .inr j) := by
    funext j
    simp only [orderedChordTriple, a, EdgeOrder.edgeAt_middle hN g hpos hlt]
  rw [he]
  exact matching_chord_witness t a (Equiv.refl _)
    (ha.ne (by decide : (0 : Fin 3) ≠ 1)) (ha.ne (by decide : (1 : Fin 3) ≠ 2))
    (ha.ne (by decide : (2 : Fin 3) ≠ 0))

/-- Choose the three new parameters for the actual ordered list, retaining the
nonzero old-new and new-new chord factors needed by the quadratic lifts. -/
theorem exists_ordered_chord_parameters [CharZero K] [Fintype I] (hN : 5 ≤ N)
    (v : Fin N ↪ I) (t : I → K) (ht₀ : ∀ i, t i ≠ 0) (ht : Function.Injective t) :
    ∃ u : Fin 3 → K, (∀ j, u j ≠ 0) ∧
      (∀ i j, chordFactor (t i) (u j) ≠ 0) ∧
      (∀ i j, i ≠ j → chordFactor (u i) (u j) ≠ 0) ∧
      ∀ g, (chordMatrix t u (orderedChordTriple hN v g)).det ≠ 0 :=
  exists_chord_parameters t ht₀ _ (ordered_chord_witness hN v t ht)

end IdealGeneration.TripleNormal
