module

public import IdealGeneration.HyperplanePoints
public import IdealGeneration.HyperplaneSpan

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Ordinary hyperplane specialization for actual point ideals

The rank transfer uses the actual equations of the off-hyperplane points and
of their union with the embedded trace. Scalar interpolation supplies a
section of restriction, and exact division supplies its kernel.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable {K : Type*} [Field K] {m p q d : ℕ}

/-- A linear lift of trace equations together with the exact residual decomposition. -/
theorem exists_polynomial_union_section
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d)) :
    ∃ L : pointPolynomialPiece b (d + 1) →ₗ[K] Poly K (m + 2),
      (∀ t, hyperplaneRestrict K (m + 1) (L t) = t.val) ∧
      L.range ≤ pointPolynomialPiece (hyperplaneConfiguration a b) (d + 1) ∧
      ∀ v : pointPolynomialPiece (hyperplaneConfiguration a b) (d + 1),
        ∃ w : pointPolynomialPiece a d, ∃ t : pointPolynomialPiece b (d + 1),
          v.val = X 0 * w.val + L t := by
  obtain ⟨L, hL, hmem⟩ := exists_linear_union_lift a b ha hoff
  refine ⟨L, hL, hmem, ?_⟩
  intro v
  let t : pointPolynomialPiece b (d + 1) :=
    ⟨hyperplaneRestrict K (m + 1) v.val,
      pointPolynomialPiece_restrict_hyperplane_le a b (d + 1) ⟨v.val, v.property, rfl⟩⟩
  have hdiff : v.val - L t ∈ pointPolynomialPiece (hyperplaneConfiguration a b) (d + 1) :=
    (pointPolynomialPiece _ _).sub_mem v.property (hmem ⟨t, rfl⟩)
  have hzero : hyperplaneRestrict K (m + 1) (v.val - L t) = 0 := by
    rw [map_sub, hL]
    exact sub_self _
  obtain ⟨w, hw, hfac⟩ := pointPolynomialPiece_hyperplane_kernel a b ha hdiff hzero
  exact ⟨⟨w, hw⟩, t, sub_eq_iff_eq_add.mp hfac⟩

/-- The injective half of ordinary hyperplane specialization, for actual point configurations. -/
theorem ordinary_hyperplane_injective
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d))
    (hres : Function.Injective (pointMultiplication a d))
    (htrace : Function.Injective (pointMultiplication b (d + 1)))
    (hdisjoint : Disjoint
      ((coordinateProduct (pointPolynomialPiece a d)).range.map
        (hyperplaneRestrict K (m + 1)).toLinearMap)
      (pointPolynomialPiece b (d + 1))) :
    Function.Injective (pointMultiplication (hyperplaneConfiguration a b) (d + 1)) := by
  obtain ⟨L, hL, hmem, hdecomp⟩ := exists_polynomial_union_section a b ha hoff
  apply (coordinateProduct_pointPolynomialPiece_injective_iff _).mp
  exact coordinateProduct_injective_of_hyperplane
    (hyperplaneRestrict K (m + 1)) (by simp) (by intro i; simp)
    (pointPolynomialPiece a d) (pointPolynomialPiece (hyperplaneConfiguration a b) (d + 1))
    (pointPolynomialPiece b (d + 1)) L hL hdecomp
    ((coordinateProduct_pointPolynomialPiece_injective_iff a).mpr hres)
    ((coordinateProduct_pointPolynomialPiece_injective_iff b).mpr htrace) hdisjoint

/-- The surjective half of ordinary hyperplane specialization, for actual point configurations. -/
theorem ordinary_hyperplane_surjective
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d))
    (htrace : Function.Surjective (pointMultiplication b (d + 1)))
    (hspan : ((coordinateProduct (pointPolynomialPiece a d)).range.map
        (hyperplaneRestrict K (m + 1)).toLinearMap) ⊔ pointPolynomialPiece b (d + 1) =
      Forms K (m + 1) (d + 1)) :
    Function.Surjective (pointMultiplication (hyperplaneConfiguration a b) (d + 1)) := by
  obtain ⟨L, hL, hmem, hdecomp⟩ := exists_polynomial_union_section a b ha hoff
  apply (coordinateProduct_pointPolynomialPiece_surjective_iff _).mp
  let ρ := hyperplaneRestrict K (m + 1)
  let W := pointPolynomialPiece a d
  let V := pointPolynomialPiece (hyperplaneConfiguration a b) (d + 1)
  let A := pointPolynomialPiece a (d + 1)
  let P := (coordinateProduct W).range
  have hPA : P ≤ A := coordinateProduct_pointPolynomialPiece_range_le (d := d) a
  have hLA : L.range ≤ A := hmem.trans (pointPolynomialPiece_hyperplane_le_off a b (d + 1))
  have hker : A ⊓ ρ.toLinearMap.ker ≤ P := by
    rintro f ⟨hf, hzero⟩
    obtain ⟨w, hw, hfac⟩ := pointPolynomialPiece_off_kernel a ha hf hzero
    refine ⟨Fin.cons ⟨w, hw⟩ (fun _ => 0), ?_⟩
    rw [coordinateProduct_single_normal]
    exact hfac.symm
  have hAspan : A ≤ P ⊔ L.range := by
    apply submodule_le_product_sup_section ρ.toLinearMap A P
      (pointPolynomialPiece b (d + 1)) L hL hPA hLA hker
    change A.map ρ.toLinearMap ≤ P.map ρ.toLinearMap ⊔ pointPolynomialPiece b (d + 1)
    rw [show A.map ρ.toLinearMap = Forms K (m + 1) (d + 1) from
      pointPolynomialPiece_off_restrict_eq a ha hoff]
    exact le_of_eq hspan.symm
  apply coordinateProduct_surjective_of_hyperplane ρ (by simp [ρ])
    (by intro i; simp [ρ]) W V A
    (pointPolynomialPiece (hyperplaneConfiguration a b) (d + 2))
    (pointPolynomialPiece b (d + 1)) (pointPolynomialPiece b (d + 2)) L hL
  · intro w
    exact normal_mul_mem_pointPolynomialPiece_hyperplane a b w.property
  · exact hmem
  · exact hAspan
  · exact coordinateProduct_pointPolynomialPiece_range_le (d := d + 1) _
  · intro f hf
    exact pointPolynomialPiece_restrict_hyperplane_le a b (d + 2) ⟨f, hf, rfl⟩
  · exact (coordinateProduct_pointPolynomialPiece_surjective_iff b).mpr htrace
  · intro f hf hzero
    simpa only [Nat.add_assoc] using pointPolynomialPiece_hyperplane_kernel a b ha hf hzero

end IdealGeneration
