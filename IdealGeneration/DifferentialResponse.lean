module

public import IdealGeneration.DeformationGeneral

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Linear algebra for the independent-condition part of the moving-point argument. -/

noncomputable section
namespace IdealGeneration.DifferentialResponse
open Module
variable {K E U N V : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup U] [Module K U]
  [AddCommGroup N] [Module K N] [AddCommGroup V] [Module K V]

/-- A residual quotient and a split scalar functional supply every first response. -/
theorem split_response_surjective
    (A D : V →ₗ[K] K × U) (normal : N →ₗ[K] V) (e : N →ₗ[K] E)
    (scalar : E →ₗ[K] K) (drop : E →ₗ[K] U) (lift : U →ₗ[K] E)
    (L : Submodule K E) (unit : E) (c : K) (hc : c ≠ 0)
    (hunit : scalar unit = 1)
    (hliftScalar : ∀ u, scalar (lift u) = 0)
    (hliftDrop : ∀ u, drop (lift u) = u)
    (hL : ∀ l ∈ L, scalar l = 0)
    (hres : Function.Surjective (L.mkQ.comp e))
    (htrace : ∀ l ∈ L, ∃ x : V, (A x).2 = drop l)
    (hnormal : ∀ g, A (normal g) = (-scalar (e g), 0))
    (hderiv : ∀ g, (D (normal g)).2 = c • drop (e g)) :
    Function.Surjective (DeformationGeneral.response A D A.range.mkQ) := by
  have hprescribe (q : E) : ∃ g : N, e g - q ∈ L := by
    obtain ⟨g, hg⟩ := hres (L.mkQ q)
    refine ⟨g, (Submodule.Quotient.mk_eq_zero _).mp ?_⟩
    change L.mkQ (e g - q) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hg
  obtain ⟨gunit, hgunit⟩ := hprescribe unit
  have hscalarUnit : scalar (e gunit) = 1 := by
    have hh := hL (e gunit - unit) hgunit
    rw [map_sub, hunit] at hh
    exact sub_eq_zero.mp hh
  have haxis (a : K) : (a, (0 : U)) ∈ A.range := by
    refine ⟨(-a) • normal gunit, ?_⟩
    rw [map_smul, hnormal, hscalarUnit]
    ext <;> simp
  have himage (a : K) (l : E) (hl : l ∈ L) : (a, drop l) ∈ A.range := by
    obtain ⟨x, hx⟩ := htrace l hl
    have hz := A.range.sub_mem (A.mem_range_self x) (haxis (A x).1)
    have hz' : ((0 : K), drop l) ∈ A.range := by
      have he : A x - ((A x).1, (0 : U)) = (0, drop l) := by
        ext <;> simp [hx]
      rwa [he] at hz
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using A.range.add_mem (haxis a) hz'
  intro z
  obtain ⟨w, rfl⟩ := A.range.mkQ_surjective z
  let q := c⁻¹ • lift w.2
  obtain ⟨g, hg⟩ := hprescribe q
  have hscalar : scalar (e g) = 0 := by
    have hh := hL (e g - q) hg
    simpa [q, hliftScalar] using hh
  have hkernel : normal g ∈ A.ker := by
    change A (normal g) = 0
    simp [hnormal, hscalar]
  refine ⟨⟨normal g, hkernel⟩, ?_⟩
  have hdiff : D (normal g) - w ∈ A.range := by
    have hh := himage ((D (normal g)).1 - w.1) (c • (e g - q)) (L.smul_mem c hg)
    have hdrop : drop (c • (e g - q)) = (D (normal g)).2 - w.2 := by
      rw [map_smul, map_sub, smul_sub, hderiv]
      simp only [q, map_smul, hliftDrop, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [hdrop] at hh
    exact hh
  change A.range.mkQ (D (normal g)) = A.range.mkQ w
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hdiff

section Rank
variable {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]

/-- A surjective first response gives surjectivity at general nonzero parameters. -/
theorem surjective_principal_open_of_response_surjective
    (A D : (Fin 1 → K) → (V →ₗ[K] W))
    (hA : IsPolynomialFamily A) (hD : IsPolynomialFamily D)
    (hfactor : ∀ a, A a = A 0 + a 0 • D a)
    (hsurj : Function.Surjective (DeformationGeneral.response
      (A 0) (D 0) (A 0).range.mkQ)) :
    ∃ p : MvPolynomial (Fin 1) K, MvPolynomial.eval 0 p ≠ 0 ∧
      ∀ a : Fin 1 → K, a 0 ≠ 0 → MvPolynomial.eval a p ≠ 0 → Function.Surjective (A a) := by
  obtain ⟨p, hp, hgood⟩ := DeformationGeneral.rank_gain_principal_open
    A D hA hD hfactor (A 0).range.mkQ (LinearMap.range_mkQ_comp (A 0))
  refine ⟨p, hp, fun a ha hpa => ?_⟩
  have hr := hgood a ha hpa
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
  have hdim := (A 0).range.finrank_quotient_add_finrank
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have hbound := Submodule.finrank_le (A a).range
  omega

end Rank
/-- A line-parameter principal open meets the complement of every finite forbidden set. -/
theorem exists_parameter_avoiding_finite [Infinite K]
    (p : MvPolynomial (Fin 1) K) (hp : MvPolynomial.eval 0 p ≠ 0)
    (F : Set K) (hF : F.Finite) :
    ∃ t : K, t ≠ 0 ∧ MvPolynomial.eval (fun _ => t) p ≠ 0 ∧ t ∉ F := by
  have hbad : (F ∪ ({0} ∪ {t : K | MvPolynomial.eval (fun _ => t) p = 0})).Finite :=
    hF.union ((Set.finite_singleton 0).union (DeformationMatrix.finite_zero_parameters p hp))
  obtain ⟨t, ht⟩ := hbad.exists_notMem
  have hparts : t ∉ F ∧ t ≠ 0 ∧ MvPolynomial.eval (fun _ => t) p ≠ 0 := by
    simpa only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, not_or] using ht
  exact ⟨t, hparts.2.1, hparts.2.2, hparts.1⟩

end IdealGeneration.DifferentialResponse
