module

public import IdealGeneration.MultiplicationOpen
public import IdealGeneration.PointAvoidance
public import IdealGeneration.Rank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Fixed partial trace conditions

The quotient by the prescribed subspace records the partial condition. The
linear-algebra construction below moves an evaluation image by an actual
automorphism, with the prescribed subspace kept fixed throughout.
-/

noncomputable section
namespace IdealGeneration
open Module MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Transversality

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- There is a linear map of the largest possible rank between two finite
dimensional vector spaces. -/
theorem exists_maximalRank_linearMap : ∃ f : V →ₗ[K] W, HasMaximalRank f := by
  by_cases h : finrank K V ≤ finrank K W
  · obtain ⟨f, hf⟩ := finrank_le_iff_exists_linearMap.mp h
    exact ⟨f, Or.inl hf⟩
  · obtain ⟨g, hg⟩ := finrank_le_iff_exists_linearMap.mp (Nat.le_of_not_ge h)
    obtain ⟨f, hf⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg)
    refine ⟨f, Or.inr ?_⟩
    intro w
    exact ⟨g w, LinearMap.congr_fun hf w⟩

/-- A linear endomorphism can put a subspace in maximal position with respect
to a fixed quotient, before requiring the endomorphism to be invertible. -/
theorem exists_endomorphism_quotient_maximalRank
    (U L : Submodule K V) :
    ∃ f : V →ₗ[K] V, HasMaximalRank ((L.mkQ.comp f).comp U.subtype) := by
  obtain ⟨g, hg⟩ := exists_maximalRank_linearMap (K := K) (V := U) (W := V ⧸ L)
  obtain ⟨s, hs⟩ := L.mkQ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr L.mkQ_surjective)
  obtain ⟨f, hf⟩ := (s.comp g).exists_extend
  refine ⟨f, ?_⟩
  have heq : (L.mkQ.comp f).comp U.subtype = g := by
    ext u
    change L.mkQ (f u.val) = g u
    rw [show f u.val = s (g u) from LinearMap.congr_fun hf u]
    exact LinearMap.congr_fun hs (g u)
  rw [heq]
  exact hg

/-- An automorphism puts any evaluation image in maximal position relative
to the fixed partial-condition subspace. -/
theorem exists_linearEquiv_quotient_maximalRank [Infinite K]
    (U L : Submodule K V) :
    ∃ e : V ≃ₗ[K] V,
      HasMaximalRank ((L.mkQ.comp e.toLinearMap).comp U.subtype) := by
  classical
  let b := Module.finBasis K (V →ₗ[K] V)
  let F : (Fin (finrank K (V →ₗ[K] V)) → K) →ₗ[K] (V →ₗ[K] V) :=
    b.equivFun.symm.toLinearMap
  let Q : (V →ₗ[K] V) →ₗ[K] (U →ₗ[K] V ⧸ L) :=
    { toFun := fun f => (L.mkQ.comp f).comp U.subtype
      map_add' := by intro f g; ext u; simp
      map_smul' := by intro c f; ext u; simp }
  obtain ⟨f, hf⟩ := exists_endomorphism_quotient_maximalRank U L
  obtain ⟨D, hD, hgoodD⟩ := rank_polynomial_principal_open
    (fun a => Q (F a)) (isPolynomialFamily_linear (Q.comp F)) (b.equivFun f)
  obtain ⟨E, hE, hgoodE⟩ := injective_polynomial_principal_open
    (fun a => F a) (isPolynomialFamily_linear F) (b.equivFun LinearMap.id)
    (by simpa only [F, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
      using (show Function.Injective (LinearMap.id : V →ₗ[K] V) from fun _ _ h => h))
  have hDne : D ≠ 0 := by intro hz; simp [hz] at hD
  have hEne : E ≠ 0 := by intro hz; simp [hz] at hE
  obtain ⟨a, ha⟩ := nonempty_principal_intersection
    (fun j : Bool => if j then D else E) (by intro j; cases j <;> simp [hDne, hEne])
  have haD : eval a D ≠ 0 := by simpa using ha true
  have haE : eval a E ≠ 0 := by simpa using ha false
  let e := LinearEquiv.ofInjectiveEndo (F a) (hgoodE a haE)
  refine ⟨e, ?_⟩
  apply (maximalRank_iff_rank_eq_min _).mpr
  have hlower := hgoodD a haD
  have hfr : finrank K (Q (F (b.equivFun f))).range =
      min (finrank K U) (finrank K (V ⧸ L)) := by
    change finrank K (Q (b.equivFun.symm (b.equivFun f))).range = _
    rw [LinearEquiv.symm_apply_apply]
    exact (maximalRank_iff_rank_eq_min _).mp hf
  rw [hfr] at hlower
  have hupper := le_min (LinearMap.finrank_range_le (Q (F a)))
    (Submodule.finrank_le (Q (F a)).range)
  change finrank K (Q (F a)).range = _
  exact le_antisymm hupper hlower

omit [FiniteDimensional K W] in
/-- The same transversality statement applies directly to a maximal-rank
evaluation map. -/
theorem exists_linearEquiv_comp_quotient_maximalRank [Infinite K]
    (L : Submodule K V) (g : W →ₗ[K] V) (hg : HasMaximalRank g) :
    ∃ e : V ≃ₗ[K] V, HasMaximalRank ((L.mkQ.comp e.toLinearMap).comp g) := by
  rcases hg with hi | hs
  · obtain ⟨e, he⟩ := exists_linearEquiv_quotient_maximalRank g.range L
    refine ⟨e, ?_⟩
    rcases he with hei | hes
    · left
      intro x y hxy
      apply hi
      have heq : g.rangeRestrict x = g.rangeRestrict y := hei hxy
      exact congrArg Subtype.val heq
    · right
      intro z
      obtain ⟨v, hv⟩ := hes z
      obtain ⟨w, hw⟩ := g.surjective_rangeRestrict v
      refine ⟨w, ?_⟩
      have hv' : L.mkQ (e v.val) = z := hv
      rw [← hw] at hv'
      exact hv' 
  · refine ⟨LinearEquiv.refl K V, Or.inr ?_⟩
    intro z
    obtain ⟨v, hv⟩ := L.mkQ_surjective z
    obtain ⟨w, hw⟩ := hs v
    refine ⟨w, ?_⟩
    change L.mkQ (g w) = z
    rw [hw]
    exact hv

end Transversality

section KernelDimensions

variable {K V W Q : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- The joint kernel is the kernel of the second map restricted to the first
kernel. -/
def prodKernelEquiv (A : V →ₗ[K] W) (B : V →ₗ[K] Q) :
    (A.prod B).ker ≃ₗ[K] (B.comp A.ker.subtype).ker where
  toFun f := ⟨⟨f.val, by
    exact congrArg Prod.fst (LinearMap.mem_ker.mp f.property)⟩, by
    exact congrArg Prod.snd (LinearMap.mem_ker.mp f.property)⟩
  invFun f := ⟨f.val.val, by
    apply LinearMap.mem_ker.mpr
    exact Prod.ext (LinearMap.mem_ker.mp f.val.property)
      (LinearMap.mem_ker.mp f.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An independent partial condition subtracts its quotient dimension from
the residual kernel, with truncation at zero. -/
theorem finrank_prod_kernel_of_restriction_maximalRank
    (A : V →ₗ[K] W) (B : V →ₗ[K] Q)
    (h : HasMaximalRank (B.comp A.ker.subtype)) :
    finrank K (A.prod B).ker = finrank K A.ker - finrank K Q := by
  rw [(prodKernelEquiv A B).finrank_eq]
  exact kernel_finrank_of_maximalRank _ h

end KernelDimensions

variable {K : Type*} [Field K] {n p d : ℕ}

local instance fixedTraceRelationGroup : AddCommGroup (EulerRelations K n d) :=
  Module.addCommMonoidToAddCommGroup K

local instance fixedTraceSubmoduleGroup (B : Submodule K (EulerRelations K n d)) :
    AddCommGroup B := Module.addCommMonoidToAddCommGroup K

/-- The independent coordinates of an Euler relation evaluated at a fixed
affine point. The omitted last coordinate is determined by the Euler relation. -/
def eulerTraceAt (y : Fin n → K) (d : ℕ) :
    EulerRelations K n d →ₗ[K] (Fin n → K) :=
  LinearMap.pi (fun j =>
    (evaluationLinear K (n + 1) d (Fin.snoc y 1)).comp
      ((LinearMap.proj j.castSucc).comp (formMultiplication K (n + 1) d).ker.subtype))

/-- Evaluate the independent fiber coordinates at all points. -/
def eulerTraceEvaluation (a : PointCoordinates K n p) (d : ℕ) :
    EulerRelations K n d →ₗ[K] (Fin p → Fin n → K) :=
  LinearMap.pi (fun i => eulerTraceAt (fun j => a (i, j)) d)

/-- Full conditions at the moving points and a partial condition at the fixed
point, represented as one linear map into a fixed finite-dimensional space. -/
def fixedPartialTraceEvaluation (y : Fin n → K)
    (L : Submodule K (Fin n → K)) (a : PointCoordinates K n p) (d : ℕ) :
    EulerRelations K n d →ₗ[K]
      ((Fin p → Fin n → K) × ((Fin n → K) ⧸ L)) :=
  (eulerTraceEvaluation a d).prod (L.mkQ.comp (eulerTraceAt y d))

/-- The reduced-coordinate Euler evaluation is a polynomial family. -/
theorem eulerTraceEvaluation_isPolynomialFamily (n p d : ℕ) :
    IsPolynomialFamily (fun a : PointCoordinates K n p => eulerTraceEvaluation a d) := by
  let P : (Fin (n + 1) → Fin p → K) →ₗ[K] (Fin p → Fin n → K) :=
    { toFun := fun f i j => f j.castSucc i
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl }
  apply isPolynomialFamily_linearMap (K := K)
    (V := EulerRelations K n d) (W := Fin p → Fin n → K)
  intro f
  have h := ((eulerEvaluation_isPolynomialFamily (K := K) n p d).linear_comp
    (LinearMap.applyₗ (R := K) (M₂ := Fin (n + 1) → Fin p → K) f)).linear_comp P
  convert h using 1
  funext a i j
  rfl

/-- A fixed quotient condition preserves polynomial dependence on the
remaining point coordinates. -/
theorem fixedPartialTraceEvaluation_isPolynomialFamily (y : Fin n → K)
    (L : Submodule K (Fin n → K)) :
    IsPolynomialFamily (fun a : PointCoordinates K n p =>
      fixedPartialTraceEvaluation y L a d) := by
  apply isPolynomialFamily_linearMap (K := K) (V := EulerRelations K n d)
    (W := (Fin p → Fin n → K) × ((Fin n → K) ⧸ L))
  intro f
  exact ((eulerTraceEvaluation_isPolynomialFamily (K := K) n p d).linear_comp
    (LinearMap.applyₗ (R := K) (M₂ := Fin p → Fin n → K) f)).prod_mk
    (isPolynomialFamily_const (L.mkQ (eulerTraceAt y d f)))

/-- The dimension predicted by a fixed partial trace condition. -/
def fixedPartialTraceDimension (L : Submodule K (Fin n → K)) (d p : ℕ) : ℕ :=
  finrank K (EulerRelations K n d) - n * p - (n - finrank K L)

/-- A maximal-rank witness gives the fixed-partial dimension on a nonempty
principal open in the remaining points. -/
theorem generic_fixedPartialTrace_of_witness (y : Fin n → K)
    (L : Submodule K (Fin n → K)) (a₀ : PointCoordinates K n p)
    (h₀ : HasMaximalRank (fixedPartialTraceEvaluation y L a₀ d)) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 →
        finrank K (fixedPartialTraceEvaluation y L a d).ker =
          fixedPartialTraceDimension L d p := by
  obtain ⟨D, hD, hgood⟩ := (by
    exact rank_polynomial_principal_open (K := K)
      (V := EulerRelations K n d)
      (W := (Fin p → Fin n → K) × ((Fin n → K) ⧸ L))
      (fun a : PointCoordinates K n p => fixedPartialTraceEvaluation y L a d)
      (fixedPartialTraceEvaluation_isPolynomialFamily (d := d) y L) a₀)
  refine ⟨D, ⟨a₀, hD⟩, fun a ha => ?_⟩
  have hlower := hgood a ha
  have hr₀ : finrank K (fixedPartialTraceEvaluation y L a₀ d).range =
      min (finrank K (EulerRelations K n d))
        (finrank K ((Fin p → Fin n → K) × ((Fin n → K) ⧸ L))) := by
    exact (maximalRank_iff_rank_eq_min (K := K)
      (V := EulerRelations K n d)
      (W := (Fin p → Fin n → K) × ((Fin n → K) ⧸ L))
      (fixedPartialTraceEvaluation y L a₀ d)).mp h₀
  have hupper := le_min
    (LinearMap.finrank_range_le (fixedPartialTraceEvaluation y L a d))
    (Submodule.finrank_le (fixedPartialTraceEvaluation y L a d).range)
  have hr : finrank K (fixedPartialTraceEvaluation y L a d).range =
      min (finrank K (EulerRelations K n d))
        (finrank K ((Fin p → Fin n → K) × ((Fin n → K) ⧸ L))) :=
    le_antisymm hupper (hr₀ ▸ hlower)
  have hk : finrank K (fixedPartialTraceEvaluation y L a d).range +
      finrank K (fixedPartialTraceEvaluation y L a d).ker =
        finrank K (EulerRelations K n d) := by
    exact LinearMap.finrank_range_add_finrank_ker (K := K)
      (V := EulerRelations K n d)
      (V₂ := (Fin p → Fin n → K) × ((Fin n → K) ⧸ L))
      (fixedPartialTraceEvaluation y L a d)
  have hq : finrank K ((Fin n → K) ⧸ L) =
      finrank K (Fin n → K) - finrank K L := L.finrank_quotient
  have ht : finrank K (((Fin p → Fin n → K) × ((Fin n → K) ⧸ L))) =
      n * p + (n - finrank K L) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.mul_one] at hq ⊢
    rw [hq, Nat.mul_comm]
    norm_num
  rw [hr, ht] at hk
  unfold fixedPartialTraceDimension
  omega

/-- The kernel is precisely the polynomial Euler relations satisfying all
full point conditions and the prescribed partial trace condition. -/
theorem mem_fixedPartialTraceEvaluation_ker
    (y : Fin n → K) (L : Submodule K (Fin n → K))
    (a : PointCoordinates K n p) (f : EulerRelations K n d) :
    f ∈ (fixedPartialTraceEvaluation y L a d).ker ↔
      (∀ (i : Fin p) (j : Fin n), eval (chartPoint K a i) (f.val j.castSucc).val = 0) ∧
      eulerTraceAt y d f ∈ L := by
  change (eulerTraceEvaluation a d f, L.mkQ (eulerTraceAt y d f)) = 0 ↔ _
  constructor
  · intro h
    have hfirst : eulerTraceEvaluation a d f = 0 := congrArg Prod.fst h
    have hlast : L.mkQ (eulerTraceAt y d f) = 0 := congrArg Prod.snd h
    refine ⟨fun i j => congrFun (congrFun hfirst i) j, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero _).mp hlast
  · rintro ⟨h, hy⟩
    apply Prod.ext
    · exact funext (fun i => funext (fun j => h i j))
    · exact (Submodule.Quotient.mk_eq_zero _).mpr hy

end IdealGeneration
