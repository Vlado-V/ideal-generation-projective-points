module

public import IdealGeneration.QuadraticUntouchedBaseClearing

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual projected generators of the untouched pairs in (A.5). -/

noncomputable section
namespace IdealGeneration.QuadraticElimination.QuadraticLiftParameters
open MvPolynomial QuadraticFlag Untouched
open scoped Classical

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]

/-- The other index in the same paired base block. -/
def partner (i : P × Bool) : P × Bool := (i.1, !i.2)

omit [Fintype P] in
theorem partner_ne (i : P × Bool) : partner i ≠ i := by
  rcases i with ⟨p, b⟩
  cases b <;> simp [partner]

/-- The layer-only coefficient of the partner direction in (A.5). -/
def pairGamma (D : QuadraticLiftParameters K P J) (i : P × Bool) (r : Fin 2) : J → K :=
  fun j => (D.clearedSecond i r j - D.slope i * D.clearedFirst i r j) /
    (D.slope (partner i) - D.slope i)

/-- The layer-only coefficient of the original direction. -/
def pairAlpha (D : QuadraticLiftParameters K P J) (i : P × Bool) (r : Fin 2) : J → K :=
  D.clearedFirst i r - D.pairGamma i r

omit [Fintype P] in
theorem layerForm_homogeneous (v : J → K) :
    (layerForm (I := P × Bool) v).IsHomogeneous 1 := by
  rw [layerForm_apply]
  exact (homogeneousSubmodule ((P × Bool) ⊕ J) K 1).sum_mem
    (fun j _ => (isHomogeneous_X K (Sum.inr j)).C_mul (v j))

/-- The scalar quadratic common to both components of the pair vector. -/
def pairContrast (i : P × Bool) (v : J → K) : MvPolynomial ((P × Bool) ⊕ J) K :=
  (y i - y (partner i)) * layerForm v

omit [Fintype P] in
theorem pairContrast_homogeneous (i : P × Bool) (v : J → K) :
    (pairContrast i v).IsHomogeneous 2 :=
  ((isHomogeneous_X K (Sum.inl i)).sub
    (isHomogeneous_X K (Sum.inl (partner i)))).mul (layerForm_homogeneous v)

omit [Fintype P] in
theorem pairContrast_mem_flagVanishing (i : P × Bool) (v : J → K) :
    pairContrast i v ∈ flagVanishing := by
  classical
  change ∀ t, eval (flagPoint t) (pairContrast i v) = 0
  intro t
  rcases i with ⟨p, b⟩
  cases t with
  | base k => simp [pairContrast, y, layerForm_apply, flagPoint, coordinatePoint]
  | basePair k l => simp [pairContrast, y, layerForm_apply, flagPoint, coordinatePoint]
  | layer j => simp [pairContrast, y, flagPoint, coordinatePoint]
  | layerPair q j =>
    cases b <;> simp [pairContrast, y, partner, flagPoint, coordinatePoint, add_comm]

variable (D : QuadraticLiftParameters K P J)

/-- The residual pair in the partner direction after removing the two mixed products. -/
def pairResidual (i : P × Bool) (r : Fin 2) :
    MvPolynomial ((P × Bool) ⊕ J) K × MvPolynomial ((P × Bool) ⊕ J) K :=
  (pairContrast i (D.pairGamma i r), C (D.slope (partner i)) * pairContrast i (D.pairGamma i r))

/-- The layer remainder separates into two mixed products and the flag-vanishing contrast. -/
theorem pair_layer_decomposition (hc : Function.Injective D.slope) (i : P × Bool)
    (r : Fin 2) (hi : i.1 ≠ D.distinguishedPair) :
    (y i * layerForm (D.clearedFirst i r), y i * layerForm (D.clearedSecond i r)) =
      generatorProduct D.slope D.firstCorrection D.secondCorrection i (layerForm (D.pairAlpha i r)) +
      generatorProduct D.slope D.firstCorrection D.secondCorrection (partner i)
        (layerForm (D.pairGamma i r)) + D.pairResidual i r := by
  have hne : D.slope (partner i) - D.slope i ≠ 0 :=
    sub_ne_zero.mpr (fun h => partner_ne i (hc h))
  have h₁ : D.clearedFirst i r = D.pairAlpha i r + D.pairGamma i r := by
    rw [pairAlpha, sub_add_cancel]
  have h₂ : D.clearedSecond i r =
      D.slope i • D.pairAlpha i r + D.slope (partner i) • D.pairGamma i r := by
    funext j
    change D.clearedSecond i r j =
      D.slope i * (D.clearedFirst i r j - D.pairGamma i r j) +
        D.slope (partner i) * D.pairGamma i r j
    have hj : D.pairGamma i r j * (D.slope (partner i) - D.slope i) =
        D.clearedSecond i r j - D.slope i * D.clearedFirst i r j :=
      (div_mul_cancel₀ _ hne)
    linear_combination -hj
  have hk : (partner i).1 ≠ D.distinguishedPair := hi
  apply Prod.ext
  · change y i * layerForm (D.clearedFirst i r) = _
    rw [h₁, map_add]
    simp only [Prod.fst_add, generatorProduct, D.firstGenerator_untouched i hi,
      D.firstGenerator_untouched (partner i) hk, pairResidual, pairContrast]
    ring
  · change y i * layerForm (D.clearedSecond i r) = _
    rw [h₂, map_add, map_smul, map_smul]
    simp only [Prod.snd_add, generatorProduct, D.secondGenerator_untouched i hi,
      D.secondGenerator_untouched (partner i) hk, pairResidual, pairContrast,
      Algebra.smul_def, MvPolynomial.algebraMap_eq]
    ring

/-- The mixed part of the raw pair can be subtracted to leave exactly the contrast. -/
theorem rawPair_sub_pairResidual_mem_mixedImage (hc : Function.Injective D.slope)
    (i : P × Bool) (r : Fin 2) (hi : i.1 ≠ D.distinguishedPair) :
    D.rawPair i r - D.pairResidual i r ∈ mixedImage D.slope D.firstCorrection D.secondCorrection := by
  rw [D.rawPair_base_clearing i r hi, D.pair_layer_decomposition hc i r hi,
    ← add_assoc, add_sub_cancel_right]
  exact Submodule.add_mem _ (D.baseCorrectionPair_mem i r)
    (Submodule.add_mem _
      (generatorProduct_mem_mixedImage _ _ _ i _ (layerForm_homogeneous _))
      (generatorProduct_mem_mixedImage _ _ _ (partner i) _ (layerForm_homogeneous _)))

/-- The contrast, recorded as a pair of quadrics in the scalar flag ideal. -/
def pairResidualFlag (i : P × Bool) (r : Fin 2) :
    ((quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
      (quadraticFlagVanishing (K := K) (P := P) (J := J))) := by
  let f := pairContrast i (D.pairGamma i r)
  let c := D.slope (partner i)
  have hf : f.IsHomogeneous 2 := pairContrast_homogeneous _ _
  have hv : f ∈ flagVanishing := pairContrast_mem_flagVanishing _ _
  refine ⟨(⟨f, hf⟩, ⟨C c * f, hf.C_mul c⟩), hv, ?_⟩
  change C c * f ∈ flagVanishing
  simpa [Algebra.smul_def] using (flagVanishing (K := K)).smul_mem c hv

omit [Fintype P] [Fintype J] in
private theorem normal₀_ne (j : J) : D.normal₀ j ≠ 0 := by
  intro h
  have hd := D.determinant_ne j
  simp [h] at hd

omit [Fintype P] [Fintype J] in
private theorem normal₁_ne (j : J) : D.normal₁ j ≠ 0 := by
  intro h
  have hd := D.determinant_ne j
  simp [h] at hd

/-- The projected elimination map with the actual lifts and corrections substituted. -/
def actualProjectedPairMap (hc : Function.Injective D.slope) :=
  projectedEliminatedMap D.slope D.firstCorrection D.secondCorrection D.distinguishedPair
    D.normal₀ D.normal₁ hc D.normal₀_ne D.normal₁_ne D.first_normal_equation D.second_normal_equation
    D.firstLift D.secondLift D.firstLift_homogeneous D.secondLift_homogeneous D.actualNormalLiftVanishing

/-- The actual projection on the two untouched inputs is the explicit contrast (A.5). -/
theorem actualProjectedPairMap_untouched (hc : Function.Injective D.slope)
    (i : P × Bool) (r : Fin 2) (hi : i.1 ≠ D.distinguishedPair) :
    D.actualProjectedPairMap hc (untouchedOmega (K := K) i r) = (D.pairResidualFlag i r).val := by
  let e := quadraticFlagSplitting D.slope D.firstCorrection D.secondCorrection D.distinguishedPair
    D.normal₀ D.normal₁ hc D.normal₀_ne D.normal₁_ne D.first_normal_equation D.second_normal_equation
  let f := phiToAllowed D.slope D.distinguishedPair D.normal₀ D.normal₁ D.firstLift D.secondLift
    (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection)
    D.firstLift_homogeneous D.secondLift_homogeneous
    (firstKernelMap_homogeneous _) (secondKernelMap_homogeneous _ _) D.actualNormalLiftVanishing
  let x := untouchedOmega (K := K) i r
  have hm := D.rawPair_sub_pairResidual_mem_mixedImage hc i r hi
  rw [← map_quadraticMixedImage] at hm
  obtain ⟨m, hm, heq⟩ := hm
  let u : quadraticMixedImage D.slope D.firstCorrection D.secondCorrection := ⟨m, hm⟩
  let w := D.pairResidualFlag i r
  have hsum : e (u, w) = f x := by
    apply Subtype.ext
    apply quadraticPairInclusion_injective
    have he : (e (u, w)).val = u.val + w.val := by
      simp only [e, quadraticFlagSplitting, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
      exact disjointSumEquiv_val _ _ _ _
    rw [he, map_add]
    change quadraticPairInclusion m + D.pairResidual i r =
      phi D.firstLift D.secondLift (firstKernelMap D.firstCorrection)
        (secondKernelMap D.slope D.secondCorrection) x
    rw [heq, sub_add_cancel, D.phi_untouchedOmega i r hi]
  change ((e.symm (f x)).2).val = w.val
  rw [← hsum, LinearEquiv.symm_apply_apply]

/-- The probe on the first coordinate of a pair and on one layer. -/
def pairProbe (p : P) (j : J) : (P × Bool) ⊕ J → K := by
  classical
  exact Sum.elim (coordinatePoint (p, false)) (coordinatePoint j)

omit [Fintype P] in
theorem eval_pairContrast_pairProbe (i : P × Bool) (v : J → K) (p : P) (j : J) :
    eval (pairProbe p j) (pairContrast i v) =
      if i.1 = p then if i.2 then -v j else v j else 0 := by
  classical
  rcases i with ⟨q, b⟩
  cases b <;> by_cases h : q = p <;>
    simp [pairProbe, pairContrast, y, partner, layerForm_apply, coordinatePoint, h]

/-- On these probes the projected pair has a scalar signed value times the partner direction. -/
theorem eval_actualProjectedPairMap_pairProbe (hc : Function.Injective D.slope)
    (i : P × Bool) (r : Fin 2) (hi : i.1 ≠ D.distinguishedPair) (p : P) (j : J) :
    let v := if i.1 = p then if i.2 then -D.pairGamma i r j else D.pairGamma i r j else 0
    let w := D.actualProjectedPairMap hc (untouchedOmega (K := K) i r)
    (eval (pairProbe p j) w.1.val, eval (pairProbe p j) w.2.val) =
      (v, D.slope (partner i) * v) := by
  rw [D.actualProjectedPairMap_untouched hc i r hi]
  simp [pairResidualFlag, eval_pairContrast_pairProbe]

omit [Fintype P] in
/-- The contrast vanishes whenever the two paired coordinates agree. -/
theorem eval_pairContrast_eq_zero_of_same (i : P × Bool) (v : J → K)
    (x : (P × Bool) ⊕ J → K) (hx : x (.inl i) = x (.inl (partner i))) :
    eval x (pairContrast i v) = 0 := by
  simp [pairContrast, y, hx]

/-- The projected pair vanishes on points with equal coordinates in its own pair. -/
theorem eval_actualProjectedPairMap_eq_zero_of_same (hc : Function.Injective D.slope)
    (i : P × Bool) (r : Fin 2) (hi : i.1 ≠ D.distinguishedPair)
    (x : (P × Bool) ⊕ J → K) (hx : x (.inl i) = x (.inl (partner i))) :
    let w := D.actualProjectedPairMap hc (untouchedOmega (K := K) i r)
    (eval x w.1.val, eval x w.2.val) = (0, 0) := by
  rw [D.actualProjectedPairMap_untouched hc i r hi]
  simp [pairResidualFlag, eval_pairContrast_eq_zero_of_same i _ x hx]

end IdealGeneration.QuadraticElimination.QuadraticLiftParameters
