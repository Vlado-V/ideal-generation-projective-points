module

public import IdealGeneration.HyperplanePoints
public import IdealGeneration.PointAvoidance
public import IdealGeneration.ScalarProductTrace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# A nonzero residual equation on the trace

When no lower-degree equation vanishes at the off-hyperplane points, restriction
of the next ideal piece is injective.  A nonzero member therefore gives a
nonempty principal open of trace points where the residual ideal evaluates
nontrivially.
-/

noncomputable section
namespace IdealGeneration.FractionalNonvanishing
open MvPolynomial Module
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {K : Type*} [Field K]

local instance pieceGroup {m z d : ℕ} (a : PointCoordinates K m z) :
    AddCommGroup (pointDegreePiece K a d) := Module.addCommMonoidToAddCommGroup K

local instance polynomialPieceGroup {m z d : ℕ} (a : PointCoordinates K m z) :
    AddCommGroup (pointPolynomialPiece a d) := Module.addCommMonoidToAddCommGroup K

/-- The absence of lower-degree equations makes restriction of the next ideal piece injective. -/
theorem offRestriction_injective_of_lower {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hlower : Function.Injective (pointEvaluation K a d)) :
    Function.Injective (offRestriction a (d + 1)) := by
  have hzero (f : pointDegreePiece K a (d + 1))
      (hf : offRestriction a (d + 1) f = 0) : f = 0 := by
    obtain ⟨g, hfg⟩ := (offRestriction_eq_zero_iff a ha f).mp hf
    have hgzero : g.val = 0 := by
      apply hlower
      have hgvan : pointEvaluation K a d g.val = 0 := g.property
      exact hgvan.trans (pointEvaluation K a d).map_zero.symm
    apply Subtype.ext
    apply Subtype.ext
    simpa only [hgzero, Submodule.coe_zero, mul_zero] using hfg
  intro f g hfg
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hfg, sub_self]

/-- A positive next-degree ideal piece contains an equation whose hyperplane restriction is nonzero. -/
theorem exists_nonzero_restriction {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hlower : Function.Injective (pointEvaluation K a d))
    (hpos : 0 < finrank K (pointDegreePiece K a (d + 1))) :
    ∃ w : pointPolynomialPiece a (d + 1), w ≠ 0 ∧
      hyperplaneRestrict K (n + 1) w.val ≠ 0 := by
  let _ : Nontrivial (pointDegreePiece K a (d + 1)) := nontrivial_of_finrank_pos hpos
  obtain ⟨f, hf⟩ := exists_ne (0 : pointDegreePiece K a (d + 1))
  refine ⟨pointPolynomialPieceEquiv a (d + 1) f, ?_, ?_⟩
  · intro hzero
    apply hf
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : pointPolynomialPiece a (d + 1) => u.val) hzero
  · intro hzero
    apply hf
    apply offRestriction_injective_of_lower a ha hlower
    apply Subtype.ext
    simpa only [pointPolynomialPieceEquiv_val, offRestriction, LinearMap.comp_apply,
      Submodule.subtype_apply, restrictForm_val, map_zero, Submodule.coe_zero] using hzero

/-- Injective multiplication forbids a nonzero residual equation from vanishing identically on the hyperplane. -/
theorem restriction_ne_zero_of_multiplication {n z e : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a e))
    (w : pointPolynomialPiece a e) (hw : w ≠ 0) :
    hyperplaneRestrict K (n + 1) w.val ≠ 0 := by
  classical
  have ha' : ∀ i, chartPoint K a i (0 : Fin (n + 2)) ≠ 0 := by
    intro i
    change chartPoint K a i (Fin.castSucc (0 : Fin (n + 1))) ≠ 0
    simpa only [chartPoint_castSucc] using ha i
  have hinj := tangentPointProduct_injective a ha' hmul
  intro hrestrict
  let g : Fin (n + 1) → pointPolynomialPiece a e := Pi.single 0 w
  have hgzero : tangentPointProduct a e g = 0 := by
    rw [tangentPointProduct_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i = 0
    · subst i
      simp only [g, Pi.single_eq_same, hrestrict, mul_zero]
    · simp [g, hi]
  have hgeq : g = 0 := hinj (hgzero.trans (map_zero _).symm)
  apply hw
  simpa [g] using congrFun hgeq 0

/-- Positive residual dimension and injective multiplication give a nonzero restricted equation. -/
theorem exists_nonzero_restriction_of_multiplication {n z e : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a e))
    (hpos : 0 < finrank K (pointDegreePiece K a e)) :
    ∃ w : pointPolynomialPiece a e, w ≠ 0 ∧
      hyperplaneRestrict K (n + 1) w.val ≠ 0 := by
  have hpos' : 0 < finrank K (pointPolynomialPiece a e) := by
    rwa [pointPolynomialPiece_finrank]
  let _ : Nontrivial (pointPolynomialPiece a e) := nontrivial_of_finrank_pos hpos'
  obtain ⟨w, hw⟩ := exists_ne (0 : pointPolynomialPiece a e)
  exact ⟨w, hw, restriction_ne_zero_of_multiplication a ha hmul w hw⟩

/-- Set the final homogeneous coordinate equal to one. -/
def chartValuePolynomial {n : ℕ} (f : Poly K (n + 1)) : MvPolynomial (Fin n) K :=
  eval₂ C (Fin.snoc (fun i => X i) 1) f

@[simp] theorem eval_chartValuePolynomial {n : ℕ} (f : Poly K (n + 1))
    (y : Fin n → K) :
    eval y (chartValuePolynomial f) = eval (Fin.snoc y 1) f := by
  rw [chartValuePolynomial, MvPolynomial.eval_eval₂]
  have hc : (eval y).comp C = RingHom.id K := by ext c; simp
  rw [hc]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- The equation restricted to the hyperplane in the normalized trace chart. -/
def traceValuePolynomial {n : ℕ} (w : Poly K (n + 2)) : MvPolynomial (Fin n) K :=
  chartValuePolynomial (hyperplaneRestrict K (n + 1) w)

@[simp] theorem eval_traceValuePolynomial {n : ℕ} (w : Poly K (n + 2))
    (y : Fin n → K) :
    eval y (traceValuePolynomial w) = eval (Fin.cons 0 (Fin.snoc y 1)) w := by
  rw [traceValuePolynomial, eval_chartValuePolynomial, eval_hyperplaneRestrict]

/-- A nonzero homogeneous restriction stays nonzero after normalization. -/
theorem traceValuePolynomial_ne_zero [Infinite K] {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (w : pointPolynomialPiece a (d + 1))
    (hw : hyperplaneRestrict K (n + 1) w.val ≠ 0) :
    traceValuePolynomial w.val ≠ 0 := by
  intro hzero
  have hhom := ((mem_pointPolynomialPiece_iff a w.val).mp w.property).1
  let f : Forms K (n + 1) (d + 1) :=
    ⟨hyperplaneRestrict K (n + 1) w.val,
      hyperplaneRestrict_homogeneous K (n + 1) hhom⟩
  have hf : f = 0 := by
    apply homogeneous_eq_zero_of_chart_evaluations
    intro y
    have he := eval_chartValuePolynomial f.val y
    change eval y (traceValuePolynomial w.val) = eval (Fin.snoc y 1) f.val at he
    simpa [hzero] using he.symm
  exact hw (congrArg Subtype.val hf)

/-- A fixed residual equation witnesses nonvanishing throughout a nonempty principal open. -/
theorem exists_nonvanishing_trace_polynomial [Infinite K] {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hlower : Function.Injective (pointEvaluation K a d))
    (hpos : 0 < finrank K (pointDegreePiece K a (d + 1))) :
    ∃ (w : pointPolynomialPiece a (d + 1)) (E : MvPolynomial (Fin n) K),
      w ≠ 0 ∧ E ≠ 0 ∧
      ∀ y : Fin n → K, eval y E = eval (Fin.cons 0 (Fin.snoc y 1)) w.val := by
  obtain ⟨w, hw, hrestrict⟩ := exists_nonzero_restriction a ha hlower hpos
  exact ⟨w, traceValuePolynomial w.val, hw,
    traceValuePolynomial_ne_zero a w hrestrict, eval_traceValuePolynomial w.val⟩

/-- A nonzero polynomial cuts out trace points with nonzero residual evaluation. -/
theorem nonvanishing_principal_open [Infinite K] {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hlower : Function.Injective (pointEvaluation K a d))
    (hpos : 0 < finrank K (pointDegreePiece K a (d + 1))) :
    ∃ E : MvPolynomial (Fin n) K, E ≠ 0 ∧
      ∀ y : Fin n → K, eval y E ≠ 0 →
        ∃ w : pointPolynomialPiece a (d + 1),
          eval (Fin.cons 0 (Fin.snoc y 1)) w.val ≠ 0 := by
  obtain ⟨w, E, _hw, hE, hEval⟩ := exists_nonvanishing_trace_polynomial a ha hlower hpos
  exact ⟨E, hE, fun y hy => ⟨w, by rwa [← hEval y]⟩⟩

/-- Nonvanishing of the residual ideal is compatible with any other nonempty trace-point open. -/
theorem exists_compatible_nonvanishing [Infinite K] {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hlower : Function.Injective (pointEvaluation K a d))
    (hpos : 0 < finrank K (pointDegreePiece K a (d + 1)))
    (P : MvPolynomial (Fin n) K) (hP : ∃ y, eval y P ≠ 0) :
    ∃ y : Fin n → K, eval y P ≠ 0 ∧
      ∃ w : pointPolynomialPiece a (d + 1),
        eval (Fin.cons 0 (Fin.snoc y 1)) w.val ≠ 0 := by
  obtain ⟨w, E, _hw, hE, hEval⟩ := exists_nonvanishing_trace_polynomial a ha hlower hpos
  have hEnonempty : ∃ y : Fin n → K, eval y E ≠ 0 := by
    by_contra! h
    exact hE (MvPolynomial.funext h)
  obtain ⟨y, hyP, hyE⟩ := principal_opens_meet P E hP hEnonempty
  exact ⟨y, hyP, w, by rwa [← hEval y]⟩

/-- Injective multiplication supplies the trace-point nonvanishing open directly. -/
theorem nonvanishing_principal_open_of_multiplication [Infinite K] {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a (d + 1)))
    (hpos : 0 < finrank K (pointDegreePiece K a (d + 1))) :
    ∃ E : MvPolynomial (Fin n) K, E ≠ 0 ∧
      ∀ y : Fin n → K, eval y E ≠ 0 →
        ∃ w : pointPolynomialPiece a (d + 1),
          eval (Fin.cons 0 (Fin.snoc y 1)) w.val ≠ 0 := by
  obtain ⟨w, _hw, hrestrict⟩ := exists_nonzero_restriction_of_multiplication a ha hmul hpos
  refine ⟨traceValuePolynomial w.val, traceValuePolynomial_ne_zero a w hrestrict, ?_⟩
  intro y hy
  exact ⟨w, by rwa [← eval_traceValuePolynomial]⟩

/-- The multiplication route to nonvanishing intersects any prescribed nonempty polynomial open. -/
theorem exists_compatible_nonvanishing_of_multiplication [Infinite K] {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a (d + 1)))
    (hpos : 0 < finrank K (pointDegreePiece K a (d + 1)))
    (P : MvPolynomial (Fin n) K) (hP : ∃ y, eval y P ≠ 0) :
    ∃ y : Fin n → K, eval y P ≠ 0 ∧
      ∃ w : pointPolynomialPiece a (d + 1),
        eval (Fin.cons 0 (Fin.snoc y 1)) w.val ≠ 0 := by
  obtain ⟨E, hE, hgood⟩ := nonvanishing_principal_open_of_multiplication a ha hmul hpos
  have hEnonempty : ∃ y : Fin n → K, eval y E ≠ 0 := by
    by_contra! h
    exact hE (MvPolynomial.funext h)
  obtain ⟨y, hyP, hyE⟩ := principal_opens_meet P E hP hEnonempty
  exact ⟨y, hyP, hgood y hyE⟩

end IdealGeneration.FractionalNonvanishing
