module

public import IdealGeneration.Multiplication
public import IdealGeneration.HyperplanePolynomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Algebra of ordinary hyperplane specialization

These lemmas prove the multiplication arguments of Lemma 3.1 directly for
subspaces of multivariate polynomial rings. The hypotheses concern residual
and trace multiplication, exact restriction and division, and transversality
of the residual product image. The conclusions concern the combined space.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- Coordinate multiplication on an arbitrary polynomial subspace. -/
def coordinateProduct {m : ℕ} (W : Submodule K (Poly K m)) :
    (Fin m → W) →ₗ[K] Poly K m where
  toFun f := ∑ i, X i * (f i).val
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum]

@[simp] theorem coordinateProduct_apply {m : ℕ} (W : Submodule K (Poly K m))
    (f : Fin m → W) : coordinateProduct W f = ∑ i, X i * (f i).val := rfl

/-- Multiplication by the normal coordinate commutes with coordinate products. -/
theorem coordinateProduct_normal {W V : Submodule K (Poly K (n + 1))}
    (hV : ∀ w : W, X (0 : Fin (n + 1)) * w.val ∈ V)
    (w : Fin (n + 1) → W) :
    coordinateProduct V (fun i => ⟨X 0 * (w i).val, hV (w i)⟩) =
      X 0 * coordinateProduct W w := by
  simp only [coordinateProduct_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A normal-coordinate-only tuple represents `X₀` times its coefficient. -/
theorem coordinateProduct_single_normal {V : Submodule K (Poly K (n + 1))}
    (v : V) : coordinateProduct V (Fin.cons v (fun _ => 0)) = X 0 * v.val := by
  simp [coordinateProduct, Fin.sum_univ_succ]

/-- The injective multiplication argument in ordinary hyperplane specialization. -/
theorem coordinateProduct_injective_of_hyperplane
    (ρ : Poly K (n + 1) →ₐ[K] Poly K n)
    (hρ₀ : ρ (X 0) = 0) (hρs : ∀ i : Fin n, ρ (X i.succ) = X i)
    (W V : Submodule K (Poly K (n + 1))) (T : Submodule K (Poly K n))
    (L : T →ₗ[K] Poly K (n + 1)) (hL : ∀ t : T, ρ (L t) = t.val)
    (hdecomp : ∀ v : V, ∃ w : W, ∃ t : T, v.val = X 0 * w.val + L t)
    (hW : Function.Injective (coordinateProduct W))
    (hT : Function.Injective (coordinateProduct T))
    (hdisjoint : Disjoint ((coordinateProduct W).range.map ρ.toLinearMap) T) :
    Function.Injective (coordinateProduct V) := by
  have hker : ∀ f : Fin (n + 1) → V, coordinateProduct V f = 0 → f = 0 := by
    intro f hf
    choose w t ht using fun i => hdecomp (f i)
    have htrace : coordinateProduct T (fun i => t i.succ) = 0 := by
      have hh := congrArg ρ hf
      simpa only [coordinateProduct_apply, map_sum, Fin.sum_univ_succ, map_mul,
        ht, map_add, hρ₀, zero_mul, zero_add, hL, hρs, map_zero] using hh
    have htangent : ∀ i : Fin n, t i.succ = 0 := by
      have hh : (fun i : Fin n => t i.succ) = 0 := hT (by simpa using htrace)
      exact fun i => congrFun hh i
    have hfactor : X (0 : Fin (n + 1)) *
        (coordinateProduct W w + L (t 0)) = 0 := by
      have heq : coordinateProduct V f =
          X (0 : Fin (n + 1)) * (coordinateProduct W w + L (t 0)) := by
        simp only [coordinateProduct_apply, Fin.sum_univ_succ, ht, htangent,
          map_zero, add_zero]
        simp only [mul_add, Finset.mul_sum]
        have hs : (∑ i : Fin n, X i.succ * (X 0 * (w i.succ).val)) =
            ∑ i : Fin n, X 0 * (X i.succ * (w i.succ).val) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hs]
        ring
      rw [← heq]
      exact hf
    have hres : coordinateProduct W w + L (t 0) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (X_ne_zero 0)
    have hresρ : ρ (coordinateProduct W w) + (t 0).val = 0 := by
      simpa only [map_add, hL, map_zero] using congrArg ρ hres
    have hu : ρ (coordinateProduct W w) ∈
        ((coordinateProduct W).range.map ρ.toLinearMap) :=
      ⟨coordinateProduct W w, ⟨w, rfl⟩, rfl⟩
    have htv : ρ (coordinateProduct W w) ∈ T := by
      rw [eq_neg_of_add_eq_zero_left hresρ]
      exact T.neg_mem (t 0).property
    have hu0 : ρ (coordinateProduct W w) = 0 :=
      (Submodule.disjoint_def.mp hdisjoint) _ hu htv
    have ht0 : t 0 = 0 := by
      apply Subtype.ext
      simpa only [hu0, zero_add, Submodule.coe_zero] using hresρ
    have hw0 : w = 0 := by
      apply hW
      simpa only [ht0, map_zero, add_zero] using hres
    funext i
    apply Subtype.ext
    rw [ht]
    have hti : t i = 0 := Fin.cases ht0 htangent i
    simp [hw0, hti]
  intro f g hfg
  have hzero : f - g = 0 := hker (f - g) (by rw [map_sub, hfg, sub_self])
  exact sub_eq_zero.mp hzero

/-- The surjective multiplication argument in ordinary hyperplane specialization.
`A` is the off-hyperplane degree-`d` ideal piece, and `Z` is the combined
configuration's degree-`d+1` ideal piece. -/
theorem coordinateProduct_surjective_of_hyperplane
    (ρ : Poly K (n + 1) →ₐ[K] Poly K n)
    (_hρ₀ : ρ (X 0) = 0) (hρs : ∀ i : Fin n, ρ (X i.succ) = X i)
    (W V A Z : Submodule K (Poly K (n + 1)))
    (T ZH : Submodule K (Poly K n))
    (L : T →ₗ[K] Poly K (n + 1)) (hL : ∀ t : T, ρ (L t) = t.val)
    (hVW : ∀ w : W, X (0 : Fin (n + 1)) * w.val ∈ V)
    (hVL : L.range ≤ V)
    (hspan : A ≤ (coordinateProduct W).range ⊔ L.range)
    (hproducts : (coordinateProduct V).range ≤ Z)
    (hrestrict : ∀ f ∈ Z, ρ f ∈ ZH)
    (htrace : ZH ≤ (coordinateProduct T).range)
    (hdivide : ∀ f ∈ Z, ρ f = 0 → ∃ a ∈ A, f = X (0 : Fin (n + 1)) * a) :
    Z ≤ (coordinateProduct V).range := by
  intro f hf
  obtain ⟨t, ht⟩ := htrace (hrestrict f hf)
  let lifted : Fin (n + 1) → V :=
    Fin.cons 0 (fun i => ⟨L (t i), hVL ⟨t i, rfl⟩⟩)
  let g := coordinateProduct V lifted
  have hg : g ∈ (coordinateProduct V).range := ⟨lifted, rfl⟩
  have hgρ : ρ g = ρ f := by
    dsimp [g, lifted]
    simpa only [coordinateProduct_apply, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Submodule.coe_zero, mul_zero, zero_add,
      map_sum, map_mul, hρs, hL] using ht
  have hfgZ : f - g ∈ Z := Z.sub_mem hf (hproducts hg)
  have hfgρ : ρ (f - g) = 0 := by rw [map_sub, hgρ, sub_self]
  obtain ⟨a, ha, hfa⟩ := hdivide (f - g) hfgZ hfgρ
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (hspan ha)
  obtain ⟨w, rfl⟩ := hu
  obtain ⟨s, rfl⟩ := hv
  have hnormalW : X (0 : Fin (n + 1)) * coordinateProduct W w ∈
      (coordinateProduct V).range := by
    refine ⟨fun i => ⟨X 0 * (w i).val, hVW (w i)⟩, ?_⟩
    exact coordinateProduct_normal hVW w
  have hnormalL : X (0 : Fin (n + 1)) * L s ∈ (coordinateProduct V).range := by
    let vs : V := ⟨L s, hVL ⟨s, rfl⟩⟩
    exact ⟨Fin.cons vs (fun _ => 0), coordinateProduct_single_normal vs⟩
  have haimage : X (0 : Fin (n + 1)) * a ∈ (coordinateProduct V).range := by
    rw [← huv, mul_add]
    exact (coordinateProduct V).range.add_mem hnormalW hnormalL
  have hfga : f - g ∈ (coordinateProduct V).range := hfa ▸ haimage
  have hsum := (coordinateProduct V).range.add_mem hfga hg
  simpa only [sub_add_cancel] using hsum

/-- Place a residual coefficient in the normal-coordinate slot. -/
def normalCoefficient (W : Submodule K (Poly K (n + 1))) :
    W →ₗ[K] (Fin (n + 1) → W) where
  toFun w := Fin.cons w (fun _ => 0)
  map_add' w v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem normalCoefficient_injective (W : Submodule K (Poly K (n + 1))) :
    Function.Injective (normalCoefficient W) := by
  intro w v h
  exact congrFun h 0

@[simp] theorem coordinateProduct_normalCoefficient
    (W : Submodule K (Poly K (n + 1))) (w : W) :
    coordinateProduct W (normalCoefficient W w) = X 0 * w.val :=
  coordinateProduct_single_normal w

/-- The kernel of restricting residual products consists exactly of the normal slot. -/
theorem restricted_coordinateProduct_ker
    (ρ : Poly K (n + 1) →ₐ[K] Poly K n) (hρ₀ : ρ (X 0) = 0)
    (W : Submodule K (Poly K (n + 1)))
    (hW : Function.Injective (coordinateProduct W))
    (hdivide : ∀ f ∈ (coordinateProduct W).range, ρ f = 0 →
      ∃ w : W, f = X 0 * w.val) :
    (ρ.toLinearMap.comp (coordinateProduct W)).ker = (normalCoefficient W).range := by
  ext f
  constructor
  · intro hf
    have hfρ : ρ (coordinateProduct W f) = 0 := hf
    obtain ⟨w, hw⟩ := hdivide _ ⟨f, rfl⟩ hfρ
    refine ⟨w, ?_⟩
    apply hW
    simpa only [coordinateProduct_normalCoefficient] using hw.symm
  · rintro ⟨w, rfl⟩
    change ρ (coordinateProduct W (normalCoefficient W w)) = 0
    rw [coordinateProduct_normalCoefficient, map_mul, hρ₀, zero_mul]

/-- The residual product loses precisely one copy of `W` under restriction. -/
theorem finrank_restricted_coordinateProduct
    (ρ : Poly K (n + 1) →ₐ[K] Poly K n) (hρ₀ : ρ (X 0) = 0)
    (W : Submodule K (Poly K (n + 1))) [FiniteDimensional K W]
    (hW : Function.Injective (coordinateProduct W))
    (hdivide : ∀ f ∈ (coordinateProduct W).range, ρ f = 0 →
      ∃ w : W, f = X 0 * w.val) :
    Module.finrank K ((coordinateProduct W).range.map ρ.toLinearMap) =
      n * Module.finrank K W := by
  let P := ρ.toLinearMap.comp (coordinateProduct W)
  have hk : Module.finrank K P.ker = Module.finrank K W := by
    rw [restricted_coordinateProduct_ker ρ hρ₀ W hW hdivide]
    exact LinearMap.finrank_range_of_inj (normalCoefficient_injective W)
  have hn := P.finrank_range_add_finrank_ker
  rw [hk] at hn
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hn
  rw [← LinearMap.range_comp]
  change Module.finrank K P.range = n * Module.finrank K W
  nlinarith

/-- The homogeneous point-ideal piece viewed in the ambient polynomial ring. -/
def pointPolynomialPiece {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) :
    Submodule K (Poly K (m + 1)) :=
  (pointDegreePiece K a d).map (Forms K (m + 1) d).subtype

/-- Forgetting the nested subtype gives an equivalence with the polynomial subspace. -/
def pointPolynomialPieceEquiv {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) :
    pointDegreePiece K a d ≃ₗ[K] pointPolynomialPiece a d :=
  Submodule.equivMapOfInjective (Forms K (m + 1) d).subtype
    (Submodule.injective_subtype _) (pointDegreePiece K a d)

@[simp] theorem pointPolynomialPieceEquiv_val {m p d : ℕ}
    (a : PointCoordinates K m p) (f : pointDegreePiece K a d) :
    (pointPolynomialPieceEquiv a d f).val = f.val.val := rfl

instance pointPolynomialPiece_finite {m p d : ℕ} (a : PointCoordinates K m p) :
    FiniteDimensional K (pointPolynomialPiece a d) :=
  Module.Finite.equiv (pointPolynomialPieceEquiv a d)

/-- Passing from nested homogeneous subtypes to polynomial subspaces preserves dimension. -/
theorem pointPolynomialPiece_finrank {m p d : ℕ} (a : PointCoordinates K m p) :
    Module.finrank K (pointPolynomialPiece a d) =
      Module.finrank K (pointDegreePiece K a d) :=
  (pointPolynomialPieceEquiv a d).finrank_eq.symm

/-- Membership in the polynomial subspace is homogeneity and vanishing at the points. -/
theorem mem_pointPolynomialPiece_iff {m p d : ℕ} (a : PointCoordinates K m p)
    (f : Poly K (m + 1)) :
    f ∈ pointPolynomialPiece a d ↔
      f.IsHomogeneous d ∧ ∀ i, eval (chartPoint K a i) f = 0 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.property, (mem_pointDegreePiece a g).mp hg⟩
  · rintro ⟨hhom, hvan⟩
    exact ⟨⟨f, hhom⟩, (mem_pointDegreePiece a _).mpr hvan, rfl⟩

/-- Coordinate multiplication agrees with multiplication on the actual ideal pieces. -/
theorem coordinateProduct_pointPolynomialPiece {m p d : ℕ}
    (a : PointCoordinates K m p) (f : Fin (m + 1) → pointDegreePiece K a d) :
    coordinateProduct (pointPolynomialPiece a d)
        (fun i => pointPolynomialPieceEquiv a d (f i)) =
      (pointMultiplication a d f).val.val := rfl

/-- Polynomial-space and homogeneous-piece formulations have the same injectivity. -/
theorem coordinateProduct_pointPolynomialPiece_injective_iff {m p d : ℕ}
    (a : PointCoordinates K m p) :
    Function.Injective (coordinateProduct (pointPolynomialPiece a d)) ↔
      Function.Injective (pointMultiplication a d) := by
  let e := pointPolynomialPieceEquiv a d
  constructor
  · intro h f g hfg
    have hh : (fun i => e (f i)) = fun i => e (g i) := h
      (congrArg (fun q : pointDegreePiece K a (d + 1) => q.val.val) hfg)
    funext i
    exact e.injective (congrFun hh i)
  · intro h f g hfg
    choose f' hf' using fun i => e.surjective (f i)
    choose g' hg' using fun i => e.surjective (g i)
    have hf : (fun i => e (f' i)) = f := funext hf'
    have hg : (fun i => e (g' i)) = g := funext hg'
    have hfg' : pointMultiplication a d f' = pointMultiplication a d g' := by
      apply Subtype.ext
      apply Subtype.ext
      rw [← coordinateProduct_pointPolynomialPiece, ← coordinateProduct_pointPolynomialPiece]
      change coordinateProduct (pointPolynomialPiece a d) (fun i => e (f' i)) =
        coordinateProduct (pointPolynomialPiece a d) (fun i => e (g' i))
      rwa [hf, hg]
    rw [← hf, ← hg, h hfg']

/-- The polynomial image contains the next ideal piece exactly when multiplication is onto. -/
theorem coordinateProduct_pointPolynomialPiece_surjective_iff {m p d : ℕ}
    (a : PointCoordinates K m p) :
    pointPolynomialPiece a (d + 1) ≤ (coordinateProduct (pointPolynomialPiece a d)).range ↔
      Function.Surjective (pointMultiplication a d) := by
  let e := pointPolynomialPieceEquiv a d
  let e' := pointPolynomialPieceEquiv a (d + 1)
  constructor
  · intro h y
    obtain ⟨f, hf⟩ := h (e' y).property
    choose f' hf' using fun i => e.surjective (f i)
    refine ⟨f', ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [← coordinateProduct_pointPolynomialPiece]
    change coordinateProduct (pointPolynomialPiece a d) (fun i => e (f' i)) = _
    rw [show (fun i => e (f' i)) = f from funext hf']
    exact hf
  · intro h y hy
    obtain ⟨y', hy'⟩ := e'.surjective ⟨y, hy⟩
    obtain ⟨f, hf⟩ := h y'
    refine ⟨fun i => e (f i), ?_⟩
    rw [coordinateProduct_pointPolynomialPiece, hf]
    exact congrArg Subtype.val hy'

/-- Products of degree-`d` point equations are degree-`d+1` point equations. -/
theorem coordinateProduct_pointPolynomialPiece_range_le {m p d : ℕ}
    (a : PointCoordinates K m p) :
    (coordinateProduct (pointPolynomialPiece a d)).range ≤ pointPolynomialPiece a (d + 1) := by
  rintro f ⟨g, rfl⟩
  apply (mem_pointPolynomialPiece_iff a _).mpr
  constructor
  · change (∑ i, X i * (g i).val).IsHomogeneous (d + 1)
    apply IsHomogeneous.sum
    intro i _
    simpa only [Nat.add_comm] using (isHomogeneous_X (R := K) i).mul
      ((mem_pointPolynomialPiece_iff a _).mp (g i).property).1
  · intro j
    change eval (chartPoint K a j) (∑ i, X i * (g i).val) = 0
    simp only [map_sum, map_mul, eval_X]
    apply Finset.sum_eq_zero
    intro i _
    rw [((mem_pointPolynomialPiece_iff a _).mp (g i).property).2 j, mul_zero]

/-- A residual product with zero trace has a residual point equation as normal quotient. -/
theorem pointProducts_normal_division {m p d : ℕ}
    (a : PointCoordinates K m p)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (f : Poly K (m + 1))
    (hf : f ∈ (coordinateProduct (pointPolynomialPiece a d)).range)
    (hρ : hyperplaneRestrict K m f = 0) :
    ∃ w : pointPolynomialPiece a d, f = X 0 * w.val := by
  have hfpoint := coordinateProduct_pointPolynomialPiece_range_le a hf
  obtain ⟨hfhom, hfvan⟩ := (mem_pointPolynomialPiece_iff a f).mp hfpoint
  let q := f.divMonomial (Finsupp.single 0 1)
  have hqhom : q.IsHomogeneous d := homogeneous_div_normal K m f hfhom
  have hqeq : X (0 : Fin (m + 1)) * q = f :=
    normal_mul_div_of_dvd K m f ((hyperplaneRestrict_eq_zero_iff K m f).mp hρ)
  have hqvan : ∀ i, eval (chartPoint K a i) q = 0 := by
    intro i
    have hh := congrArg (eval (chartPoint K a i)) hqeq
    rw [map_mul, eval_X, hfvan i] at hh
    exact (mul_eq_zero.mp hh).resolve_left (ha i)
  exact ⟨⟨q, (mem_pointPolynomialPiece_iff a q).mpr ⟨hqhom, hqvan⟩⟩, hqeq.symm⟩

/-- The actual residual trace-product dimension in Lemma 3.1. -/
theorem finrank_restricted_pointProducts {m p d : ℕ}
    (a : PointCoordinates K m p)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (h : Function.Injective (pointMultiplication a d)) :
    Module.finrank K ((coordinateProduct (pointPolynomialPiece a d)).range.map
      (hyperplaneRestrict K m).toLinearMap) =
        m * Module.finrank K (pointDegreePiece K a d) := by
  simpa only [pointPolynomialPiece_finrank] using
    finrank_restricted_coordinateProduct (hyperplaneRestrict K m)
      (hyperplaneRestrict_X_zero K m) (pointPolynomialPiece a d)
      ((coordinateProduct_pointPolynomialPiece_injective_iff a).mpr h)
      (pointProducts_normal_division a ha)

/-- Residual products restrict to forms of the expected homogeneous degree. -/
theorem restricted_pointProducts_le_forms {m p d : ℕ}
    (a : PointCoordinates K m p) :
    (coordinateProduct (pointPolynomialPiece a d)).range.map
        (hyperplaneRestrict K m).toLinearMap ≤ Forms K m (d + 1) := by
  rintro f ⟨g, hg, rfl⟩
  exact hyperplaneRestrict_homogeneous K m
    ((mem_pointPolynomialPiece_iff a g).mp
      (coordinateProduct_pointPolynomialPiece_range_le a hg)).1

end IdealGeneration
