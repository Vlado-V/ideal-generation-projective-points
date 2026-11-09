module

public import IdealGeneration.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Polynomial restriction to a coordinate hyperplane

The normal coordinate is `0`. The trace variables are its successors. These
maps and exact decompositions concern actual homogeneous polynomials.
The coordinate-division proof generalizes the existing local
`ChoppedPlane/ToeplitzDivision.lean` development.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable (K : Type*) [Field K] (n : ℕ)

/-- Set the first coordinate to zero and retain the successor coordinates. -/
def hyperplaneRestrict : Poly K (n + 1) →ₐ[K] Poly K n :=
  MvPolynomial.aeval (Fin.cases 0 fun j => X j)

/-- Include trace polynomials as polynomials independent of the first variable. -/
def hyperplaneExtend : Poly K n →ₐ[K] Poly K (n + 1) :=
  MvPolynomial.rename Fin.succ

@[simp] theorem hyperplaneRestrict_X_zero :
    hyperplaneRestrict K n (X 0) = 0 := by simp [hyperplaneRestrict]

@[simp] theorem hyperplaneRestrict_X_succ (j : Fin n) :
    hyperplaneRestrict K n (X j.succ) = X j := by simp [hyperplaneRestrict]

@[simp] theorem hyperplaneExtend_X (j : Fin n) :
    hyperplaneExtend K n (X j) = X j.succ := by simp [hyperplaneExtend]

@[simp] theorem hyperplaneRestrict_extend (f : Poly K n) :
    hyperplaneRestrict K n (hyperplaneExtend K n f) = f := by
  have h : (hyperplaneRestrict K n).comp (hyperplaneExtend K n) = AlgHom.id K _ := by
    ext j
    simp
  exact congrArg (fun F : Poly K n →ₐ[K] Poly K n => F f) h

/-- Restriction is the constant coefficient in the normal coordinate. -/
theorem hyperplaneRestrict_eq_coeff_zero (f : Poly K (n + 1)) :
    hyperplaneRestrict K n f = (MvPolynomial.finSuccEquiv K n f).coeff 0 := by
  let r : Poly K (n + 1) →+* Poly K n :=
    Polynomial.constantCoeff.comp (MvPolynomial.finSuccEquiv K n).toRingHom
  have h : (hyperplaneRestrict K n).toRingHom = r := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [hyperplaneRestrict, r, MvPolynomial.finSuccEquiv_apply]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [r, MvPolynomial.finSuccEquiv_X_zero]
      · simp [r, MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (fun F : Poly K (n + 1) →+* Poly K n => F f) h

/-- Restriction preserves the homogeneous degree. -/
theorem hyperplaneRestrict_homogeneous {d : ℕ} {f : Poly K (n + 1)}
    (hf : f.IsHomogeneous d) : (hyperplaneRestrict K n f).IsHomogeneous d := by
  rw [hyperplaneRestrict_eq_coeff_zero]
  exact hf.finSuccEquiv_coeff_isHomogeneous 0 d (zero_add d)

/-- Extension preserves the homogeneous degree. -/
theorem hyperplaneExtend_homogeneous {d : ℕ} {f : Poly K n}
    (hf : f.IsHomogeneous d) : (hyperplaneExtend K n f).IsHomogeneous d :=
  hf.rename_isHomogeneous

/-- A polynomial restricts to zero exactly when the normal variable divides it. -/
theorem hyperplaneRestrict_eq_zero_iff (f : Poly K (n + 1)) :
    hyperplaneRestrict K n f = 0 ↔ X 0 ∣ f := by
  constructor
  · intro hf
    have hp : Polynomial.X ∣ MvPolynomial.finSuccEquiv K n f :=
      Polynomial.X_dvd_iff.mpr ((hyperplaneRestrict_eq_coeff_zero K n f).symm.trans hf)
    obtain ⟨q, hq⟩ := hp
    refine ⟨(MvPolynomial.finSuccEquiv K n).symm q, ?_⟩
    apply (MvPolynomial.finSuccEquiv K n).injective
    simpa only [map_mul, MvPolynomial.finSuccEquiv_X_zero,
      AlgEquiv.apply_symm_apply] using hq
  · rintro ⟨g, rfl⟩
    simp

/-- Removing one normal-variable factor lowers homogeneous degree by one. -/
theorem homogeneous_div_normal {d : ℕ} (f : Poly K (n + 1))
    (hf : f.IsHomogeneous (d + 1)) :
    (f.divMonomial (Finsupp.single 0 1)).IsHomogeneous d := by
  intro e he
  have hcoeff : f.coeff (Finsupp.single 0 1 + e) ≠ 0 := by
    simpa only [coeff_divMonomial] using he
  have hdeg : (Finsupp.single 0 1 + e).degree = d + 1 := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hf hcoeff
  have hedeg : e.degree = d := by
    simp only [map_add, Finsupp.degree_single] at hdeg
    omega
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hedeg

/-- The canonical quotient reconstructs a polynomial divisible by the normal variable. -/
theorem normal_mul_div_of_dvd (f : Poly K (n + 1)) (hf : X 0 ∣ f) :
    X 0 * f.divMonomial (Finsupp.single 0 1) = f := by
  have hm := (X_dvd_iff_modMonomial_eq_zero).mp hf
  simpa only [hm, add_zero] using f.divMonomial_add_modMonomial_single 0

/-- Restriction of degree-`d` forms. -/
def restrictForm (d : ℕ) : Forms K (n + 1) d →ₗ[K] Forms K n d where
  toFun f := ⟨hyperplaneRestrict K n f.val, hyperplaneRestrict_homogeneous K n f.property⟩
  map_add' _f _g := Subtype.ext (map_add _ _ _)
  map_smul' _c _f := Subtype.ext (map_smul _ _ _)

/-- Extension of degree-`d` trace forms. -/
def extendForm (d : ℕ) : Forms K n d →ₗ[K] Forms K (n + 1) d where
  toFun f := ⟨hyperplaneExtend K n f.val, hyperplaneExtend_homogeneous K n f.property⟩
  map_add' _f _g := Subtype.ext (map_add _ _ _)
  map_smul' _c _f := Subtype.ext (map_smul _ _ _)

@[simp] theorem restrictForm_val {d : ℕ} (f : Forms K (n + 1) d) :
    (restrictForm K n d f).val = hyperplaneRestrict K n f.val := rfl

@[simp] theorem extendForm_val {d : ℕ} (f : Forms K n d) :
    (extendForm K n d f).val = hyperplaneExtend K n f.val := rfl

@[simp] theorem restrictForm_extendForm {d : ℕ} (f : Forms K n d) :
    restrictForm K n d (extendForm K n d f) = f := by
  apply Subtype.ext
  exact hyperplaneRestrict_extend K n f.val

/-- Every homogeneous polynomial in the kernel has a homogeneous normal quotient. -/
theorem restrictForm_eq_zero_iff {d : ℕ} (f : Forms K (n + 1) (d + 1)) :
    restrictForm K n (d + 1) f = 0 ↔
      ∃ g : Forms K (n + 1) d, f.val = X 0 * g.val := by
  constructor
  · intro hf
    have hf' : hyperplaneRestrict K n f.val = 0 := congrArg Subtype.val hf
    have hdiv := (hyperplaneRestrict_eq_zero_iff K n f.val).mp hf'
    exact ⟨⟨f.val.divMonomial (Finsupp.single 0 1),
      homogeneous_div_normal K n f.val f.property⟩,
      (normal_mul_div_of_dvd K n f.val hdiv).symm⟩
  · rintro ⟨g, hg⟩
    apply Subtype.ext
    change hyperplaneRestrict K n f.val = 0
    rw [hg]
    simp

/-- Restriction is onto, with polynomial extension as a right inverse. -/
theorem restrictForm_surjective (d : ℕ) : Function.Surjective (restrictForm K n d) :=
  fun f => ⟨extendForm K n d f, restrictForm_extendForm K n f⟩

/-- Evaluation of an extended polynomial drops the first coordinate. -/
theorem eval_hyperplaneExtend (f : Poly K n) (x : Fin (n + 1) → K) :
    eval x (hyperplaneExtend K n f) = eval (fun j => x j.succ) f := by
  exact MvPolynomial.eval_rename _ _ _

/-- Evaluating a restricted polynomial is evaluation on the coordinate hyperplane. -/
theorem eval_hyperplaneRestrict (f : Poly K (n + 1)) (y : Fin n → K) :
    eval y (hyperplaneRestrict K n f) = eval (Fin.cons 0 y) f := by
  have h : (eval y).comp (hyperplaneRestrict K n).toRingHom = eval (Fin.cons 0 y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [hyperplaneRestrict]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp [hyperplaneRestrict]
  exact congrArg (fun F : Poly K (n + 1) →+* K => F f) h

/-- Multiplication by the normal coordinate between consecutive homogeneous spaces. -/
def normalFormMul (d : ℕ) : Forms K (n + 1) d →ₗ[K] Forms K (n + 1) (d + 1) where
  toFun f := ⟨X 0 * f.val, by
    change (X 0 * f.val).IsHomogeneous (d + 1)
    simpa only [Nat.add_comm] using (isHomogeneous_X (R := K) (0 : Fin (n + 1))).mul f.property⟩
  map_add' _f _g := Subtype.ext (mul_add _ _ _)
  map_smul' _c _f := Subtype.ext (mul_smul_comm _ _ _)

@[simp] theorem normalFormMul_val {d : ℕ} (f : Forms K (n + 1) d) :
    (normalFormMul K n d f).val = X 0 * f.val := rfl

/-- Multiplication by the normal coordinate is injective. -/
theorem normalFormMul_injective (d : ℕ) : Function.Injective (normalFormMul K n d) := by
  intro f g h
  apply Subtype.ext
  exact mul_left_cancel₀ (X_ne_zero 0) (congrArg Subtype.val h)

@[simp] theorem restrictForm_normalFormMul {d : ℕ} (f : Forms K (n + 1) d) :
    restrictForm K n (d + 1) (normalFormMul K n d f) = 0 := by
  apply Subtype.ext
  simp

/-- The polynomial extension map is injective. -/
theorem hyperplaneExtend_injective : Function.Injective (hyperplaneExtend K n) := by
  intro f g h
  simpa only [hyperplaneRestrict_extend] using congrArg (hyperplaneRestrict K n) h

/-- The homogeneous extension map is injective. -/
theorem extendForm_injective (d : ℕ) : Function.Injective (extendForm K n d) := by
  intro f g h
  simpa only [restrictForm_extendForm] using congrArg (restrictForm K n d) h

/-- The kernel of restriction is precisely the image of normal multiplication. -/
theorem restrictForm_ker_eq_range (d : ℕ) :
    LinearMap.ker (restrictForm K n (d + 1)) = LinearMap.range (normalFormMul K n d) := by
  ext f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (restrictForm_eq_zero_iff K n f).mp hf
    exact ⟨g, Subtype.ext hg.symm⟩
  · rintro ⟨g, rfl⟩
    exact restrictForm_normalFormMul K n g

/-- Every homogeneous polynomial splits into its trace and a normal multiple. -/
theorem exists_normal_split {d : ℕ} (f : Forms K (n + 1) (d + 1)) :
    ∃ g : Forms K (n + 1) d,
      f = extendForm K n (d + 1) (restrictForm K n (d + 1) f) + normalFormMul K n d g := by
  let r := f - extendForm K n (d + 1) (restrictForm K n (d + 1) f)
  have hr : restrictForm K n (d + 1) r = 0 := by
    simp [r]
  obtain ⟨g, hg⟩ := (restrictForm_eq_zero_iff K n r).mp hr
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change f.val = (extendForm K n (d + 1) (restrictForm K n (d + 1) f)).val + X 0 * g.val
  have heq : f.val - (extendForm K n (d + 1) (restrictForm K n (d + 1) f)).val = X 0 * g.val := hg
  exact sub_eq_iff_eq_add'.mp heq

end IdealGeneration
