module

public import IdealGeneration.ScalarSelection
public import IdealGeneration.DifferentialSurjectivity

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Selected scalar rows and the moving-point residual conditions

All maps below evaluate the same homogeneous polynomials. The selected row
space is allowed to depend on the entire hyperplane configuration.
-/

noncomputable section
namespace IdealGeneration.FractionalResidual
open MvPolynomial Module HyperplaneEuler DifferentialPoint
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K]

section LinearRows
variable {V I : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Independent scalar functionals prescribe arbitrary values. -/
theorem finite_rows_surjective [Fintype I] (rows : I → Module.Dual K V)
    (hrows : LinearIndependent K rows) : Function.Surjective (LinearMap.pi rows) := by
  classical
  let : Module.IsReflexive K V := Module.IsReflexive.of_finite_of_free K V
  let e := Fintype.equivFin I
  let r : Fin (Fintype.card I) → Module.Dual K V := fun i => rows (e.symm i)
  have hr : LinearIndependent K r := hrows.comp _ e.symm.injective
  obtain ⟨dual, hdual⟩ := exists_coordinate_functionals r hr
  intro b
  let x : V := ∑ i, b (e.symm i) • (Module.evalEquiv K V).symm (dual i)
  refine ⟨x, ?_⟩
  ext j
  change rows j x = b j
  have hj : rows j = r (e j) := by simp [r]
  rw [hj]
  simp [x, hdual]

end LinearRows

local instance residualPartialGroup {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (y : Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) :
    AddCommGroup (residualPartialSpace a d y L) :=
  Module.addCommMonoidToAddCommGroup K

/-- The selected hyperplane points, retaining their index subtype. -/
def selectedPoints {n p : ℕ} (P : PointCoordinates K n p) (s : Finset (Fin p)) :
    s → Fin (n + 2) → K := fun i => Fin.cons 0 (chartPoint K P i.val)

/-- Full off-hyperplane values. -/
def offEvaluation {n z d : ℕ} (a : PointCoordinates K (n + 1) z) :
    (Fin (n + 1) → Forms K (n + 2) d) →ₗ[K] (Fin z → Fin (n + 1) → K) :=
  LinearMap.pi (fun i => tupleEvaluation (chartPoint K a i))

/-- The full and partial conditions that precede scalar-row selection. -/
def baseConditions {n z d : ℕ} (a : PointCoordinates K (n + 1) z)
    (y : Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K)) :
    (Fin (n + 1) → Forms K (n + 2) d) →ₗ[K]
      (Fin z → Fin (n + 1) → K) × ((Fin (n + 1) → K) ⧸ L) :=
  (offEvaluation a).prod (L.mkQ.comp (tupleEvaluation (Fin.cons 0 y)))

/-- The selected scalar conditions on unrestricted homogeneous tuples. -/
def selectedRows {n z p d : ℕ} (_a : PointCoordinates K (n + 1) z)
    (P : PointCoordinates K n p) (s : Finset (Fin p)) :
    (Fin (n + 1) → Forms K (n + 2) d) →ₗ[K] (s → K) :=
  LinearMap.pi (fun i => (evaluationLinear K (n + 2) (d + 1)
    (Fin.cons 0 (chartPoint K P i.val))).comp (tangentProduct K (n + 1) d))

/-- Actual residual conditions, ordered as in the moving-point lemma. -/
def selectedResidualConditions {n z p d : ℕ} (a : PointCoordinates K (n + 1) z)
    (P : PointCoordinates K n p) (s : Finset (Fin p))
    (y : Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K)) :
    (Fin (n + 1) → Forms K (n + 2) d) →ₗ[K]
      ((Fin z → Fin (n + 1) → K) × (s → K)) × ((Fin (n + 1) → K) ⧸ L) :=
  ((offEvaluation a).prod (selectedRows (d := d) a P s)).prod
    (L.mkQ.comp (tupleEvaluation (Fin.cons 0 y)))

/-- A residual ideal tuple viewed as a tuple of homogeneous forms. -/
def polynomialTuple {n z d : ℕ} (a : PointCoordinates K (n + 1) z) :
    (Fin (n + 1) → pointPolynomialPiece a d) →ₗ[K]
      (Fin (n + 1) → Forms K (n + 2) d) where
  toFun w i := ⟨(w i).val, ((mem_pointPolynomialPiece_iff a (w i).val).mp (w i).property).1⟩
  map_add' _ _ := by ext i; rfl
  map_smul' _ _ := by ext i; rfl

@[simp] theorem polynomialTuple_val {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (w : Fin (n + 1) → pointPolynomialPiece a d)
    (i : Fin (n + 1)) : (polynomialTuple a w i).val = (w i).val := rfl

/-- The selected scalar rows agree under the actual polynomial identification. -/
theorem selectedRows_polynomialTuple {n z p d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (w : Fin (n + 1) → pointPolynomialPiece a d) :
    selectedRows (d := d) a P s (polynomialTuple a w) =
      fun i => residualScalarRow a d P i.val w := by
  ext i
  simp [selectedRows, evaluationLinear, tangentProduct_val, residualScalarRow_apply]

/-- The residual partial space has zero base conditions. -/
theorem polynomialTuple_base_zero {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (y : Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) (w : residualPartialSpace a d y L) :
    baseConditions (d := d) a y L (polynomialTuple a w.val) = 0 := by
  apply Prod.ext
  · ext i j
    exact ((mem_pointPolynomialPiece_iff a (w.val j).val).mp (w.val j).property).2 i
  · apply (Submodule.Quotient.mk_eq_zero L).mpr
    exact w.property

/-- Independent scalar postulation and a nonzero residual value prescribe the base conditions. -/
theorem baseConditions_surjective {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (y : Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K))
    (ha : Function.Surjective (pointEvaluation K a d))
    (hy : ∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0) :
    Function.Surjective (baseConditions (d := d) a y L) := by
  classical
  rintro ⟨u, q⟩
  obtain ⟨v, rfl⟩ := L.mkQ_surjective q
  obtain ⟨w, hw⟩ := hy
  let w' : Forms K (n + 2) d := ⟨w.val, ((mem_pointPolynomialPiece_iff a w.val).mp w.property).1⟩
  have hwzero (i : Fin z) : eval (chartPoint K a i) w'.val = 0 :=
    ((mem_pointPolynomialPiece_iff a w.val).mp w.property).2 i
  choose f hf using fun j : Fin (n + 1) => ha (fun i => u i j)
  let g : Fin (n + 1) → Forms K (n + 2) d := fun j =>
    f j + ((v j - eval (Fin.cons 0 y) (f j).val) / eval (Fin.cons 0 y) w.val) • w'
  refine ⟨g, ?_⟩
  apply Prod.ext
  · ext i j
    have hfi : eval (chartPoint K a i) (f j).val = u i j := congrFun (hf j) i
    change eval (chartPoint K a i) (g j).val = u i j
    simp only [g, Submodule.coe_add, Submodule.coe_smul, map_add,
      smul_eq_C_mul, map_mul, eval_C, hwzero, hfi, mul_zero, add_zero]
  · apply congrArg L.mkQ
    ext j
    change eval (Fin.cons 0 y) (g j).val = v j
    simp only [g, Submodule.coe_add, Submodule.coe_smul, map_add,
      smul_eq_C_mul, map_mul, eval_C]
    change eval (Fin.cons 0 y) (f j).val +
      ((v j - eval (Fin.cons 0 y) (f j).val) / eval (Fin.cons 0 y) w.val) *
        eval (Fin.cons 0 y) w.val = v j
    rw [div_mul_cancel₀ _ hw]
    ring


/-- Every zero of the base conditions is an actual residual ideal tuple. -/
theorem exists_polynomialTuple_of_base_zero {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (y : Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K))
    (g : Fin (n + 1) → Forms K (n + 2) d) (hg : baseConditions (d := d) a y L g = 0) :
    ∃ w : residualPartialSpace a d y L, polynomialTuple a w.val = g := by
  have hoff (i : Fin z) (j : Fin (n + 1)) : eval (chartPoint K a i) (g j).val = 0 :=
    congrFun (congrFun (congrArg Prod.fst hg) i) j
  let w : Fin (n + 1) → pointPolynomialPiece a d := fun j =>
    ⟨(g j).val, (mem_pointPolynomialPiece_iff a (g j).val).mpr ⟨(g j).property, fun i => hoff i j⟩⟩
  have hpartial : w ∈ residualPartialSpace a d y L := by
    apply (Submodule.Quotient.mk_eq_zero L).mp
    exact congrArg Prod.snd hg
  refine ⟨⟨w, hpartial⟩, ?_⟩
  ext j
  rfl

/-- Separating selected scalar rows kill the complete residual kernel. -/
theorem selectedResidualConditions_zero_of_selected_injective {n z p d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (y : Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K))
    (hinj : Function.Injective (selectedScalarEvaluation
      (residualPartialScalarRow a d P y L) s))
    (g : Fin (n + 1) → Forms K (n + 2) d)
    (hg : selectedResidualConditions (d := d) a P s y L g = 0) : g = 0 := by
  have hbase : baseConditions (d := d) a y L g = 0 := by
    apply Prod.ext
    · exact congrArg (fun q : ((Fin z → Fin (n + 1) → K) × (s → K)) ×
        ((Fin (n + 1) → K) ⧸ L) => q.1.1) hg
    · exact congrArg (fun q : ((Fin z → Fin (n + 1) → K) × (s → K)) ×
        ((Fin (n + 1) → K) ⧸ L) => q.2) hg
  obtain ⟨w, hw⟩ := exists_polynomialTuple_of_base_zero a y L g hbase
  have hrow : selectedScalarEvaluation (residualPartialScalarRow a d P y L) s w = 0 := by
    rw [← hw] at hg
    have hs := congrArg (fun q => q.1.2) hg
    change selectedRows (d := d) a P s (polynomialTuple a w.val) = 0 at hs
    rw [selectedRows_polynomialTuple] at hs
    exact hs
  have hwzero : w = 0 := hinj (by simpa using hrow)
  rw [hwzero] at hw
  simpa using hw.symm

/-- The selected injective rows give precisely the zero-kernel residual hypothesis of Lemma 3.4. -/
theorem differential_residual_zero_of_selected_injective {n z p d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (y : Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K))
    (hinj : Function.Injective (selectedScalarEvaluation
      (residualPartialScalarRow a d P y L) s))
    (g : Fin (n + 1) → Forms K (n + 2) d)
    (hoff : ∀ i j, eval (chartPoint K a i) (g j).val = 0)
    (hon : ∀ i : s, eval (selectedPoints P s i) (tangentProduct K (n + 1) d g).val = 0)
    (hpartial : (fun j => eval (Fin.cons 0 y) (g j).val) ∈ L) : g = 0 := by
  apply selectedResidualConditions_zero_of_selected_injective a P s y L hinj g
  apply Prod.ext
  · apply Prod.ext
    · ext i j
      exact hoff i j
    · ext i
      exact hon i
  · apply (Submodule.Quotient.mk_eq_zero L).mpr
    exact hpartial

/-- Independent scalar postulation and independent rows make all residual conditions independent. -/
theorem selectedResidualConditions_surjective_of_selected_surjective {n z p d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (y : Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K))
    (ha : Function.Surjective (pointEvaluation K a d))
    (hy : ∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0)
    (hrows : Function.Surjective (selectedScalarEvaluation
      (residualPartialScalarRow a d P y L) s)) :
    Function.Surjective (selectedResidualConditions (d := d) a P s y L) := by
  rintro ⟨⟨u, r⟩, q⟩
  obtain ⟨g, hg⟩ := baseConditions_surjective a y L ha hy (u, q)
  obtain ⟨w, hw⟩ := hrows (r - selectedRows (d := d) a P s g)
  let v := polynomialTuple a w.val
  have hvbase : baseConditions (d := d) a y L v = 0 := polynomialTuple_base_zero a y L w
  have hvalue : selectedRows (d := d) a P s v =
      selectedScalarEvaluation (residualPartialScalarRow a d P y L) s w :=
    selectedRows_polynomialTuple a P s w.val
  refine ⟨g + v, ?_⟩
  apply Prod.ext
  · apply Prod.ext
    · change offEvaluation a (g + v) = u
      rw [map_add, show offEvaluation a g = u from congrArg Prod.fst hg,
        show offEvaluation a v = 0 from congrArg Prod.fst hvbase, add_zero]
    · change selectedRows (d := d) a P s (g + v) = r
      rw [map_add, hvalue, hw]
      abel
  · change (L.mkQ.comp (tupleEvaluation (Fin.cons 0 y))) (g + v) = q
    rw [map_add, show (L.mkQ.comp (tupleEvaluation (Fin.cons 0 y))) g = q from congrArg Prod.snd hg,
      show (L.mkQ.comp (tupleEvaluation (Fin.cons 0 y))) v = 0 from congrArg Prod.snd hvbase,
      add_zero]

/-- Linear independence is the row-selection hypothesis for the surjective endpoint. -/
theorem selectedResidualConditions_surjective_of_selected_independent {n z p d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (y : Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K))
    (ha : Function.Surjective (pointEvaluation K a d))
    (hy : ∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0)
    (hrows : LinearIndependent K (fun i : s => residualPartialScalarRow a d P y L i)) :
    Function.Surjective (selectedResidualConditions (d := d) a P s y L) := by
  exact selectedResidualConditions_surjective_of_selected_surjective a P s y L ha hy
    (finite_rows_surjective _ hrows)

/-- This is exactly the residual map used by the differential hyperplane step. -/
theorem selectedResidualConditions_eq {n z p d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (y : Fin (n + 1) → K)
    (B : Submodule K (Relations K (n + 1) (d + 1))) :
    selectedResidualConditions (d := d) a P s y (traceImage B (Fin.cons 0 y)) =
      residualConditions (fun i => chartPoint K a i) (selectedPoints P s) B (Fin.cons 0 y) := by
  apply LinearMap.ext
  intro g
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · ext i
      rfl
  · rfl

/-- The selected-row independence gives the actual differential residual surjectivity. -/
theorem differential_residualConditions_surjective_of_selected_independent {n z p d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (y : Fin (n + 1) → K)
    (B : Submodule K (Relations K (n + 1) (d + 1)))
    (ha : Function.Surjective (pointEvaluation K a d))
    (hy : ∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0)
    (hrows : LinearIndependent K (fun i : s =>
      residualPartialScalarRow a d P y (traceImage B (Fin.cons 0 y)) i)) :
    Function.Surjective (residualConditions (fun i => chartPoint K a i)
      (selectedPoints P s) B (Fin.cons 0 y)) := by
  rw [← selectedResidualConditions_eq]
  exact selectedResidualConditions_surjective_of_selected_independent a P s y _ ha hy hrows

end IdealGeneration.FractionalResidual
