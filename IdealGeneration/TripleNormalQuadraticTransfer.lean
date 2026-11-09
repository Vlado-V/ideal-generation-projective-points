module

public import IdealGeneration.ConeA1Bridge
public import IdealGeneration.ConeMonomialChart

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The endpoint of the three-normal quadratic construction

The marked cone witness meets the open trace locus from the induction
hypothesis. The trace count is balanced, and the ambient count is exactly
the integral quadratic critical count.
-/

noncomputable section
namespace IdealGeneration.TripleNormal

open MvPolynomial Module ConeParameterSpace ConeMiddleFamily

variable {K : Type*} [Field K]

private theorem tripleNormalTraceBalance (m : ℕ) (hm : 1 ≤ m) (hmod : m % 3 = 0) :
    m * (N m 2 - m * (m + 1) / 3) = N m 3 - m * (m + 1) / 3 := by
  let q := m * (m + 1) / 3
  let t := m / 3
  have hmt : m = 3 * t := by dsimp [t]; omega
  have hprod : m * (m + 1) = 3 * (t * (m + 1)) := by
    calc
      m * (m + 1) = (3 * t) * (m + 1) := congrArg (fun x => x * (m + 1)) hmt
      _ = _ := Nat.mul_assoc _ _ _
  have hq : m * (m + 1) = 3 * q := by dsimp [q]; rw [hprod]; omega
  have hN₂ := N_degree_recurrence m 1 hm
  change 2 * N m 2 = (m + 1) * N m 1 at hN₂
  rw [N_one_degree, Nat.mul_comm (m + 1) m, hq] at hN₂
  let r := N m 2 - q
  have hr : N m 2 = 3 * r := by dsimp [r]; omega
  have hqr : q = 2 * r := by omega
  have hN₃ := N_degree_recurrence m 2 hm
  change 3 * N m 3 = (m + 2) * N m 2 at hN₃
  rw [hr, Nat.mul_left_comm (m + 2) 3 r] at hN₃
  have hN₃' : N m 3 = (m + 2) * r := by omega
  change m * r = N m 3 - q
  rw [hN₃', hqr, Nat.add_mul]
  omega

private theorem tripleNormalPointCount (h : ℕ) :
    (2 * h + 12) + (h + 4) * (h + 5) / 3 = (h + 7) * (h + 8) / 3 := by
  have hprod : (h + 7) * (h + 8) = (h + 4) * (h + 5) + 3 * (2 * h + 12) := by ring
  rw [hprod]
  omega

private theorem encodedPoint_ne_zero_of_normalEvaluation {m p q : ℕ}
    (C : ConeConfiguration K 3 m p q)
    (hnormal : Function.Surjective (normalEvaluation C.support (encode C) 2)) :
    ∀ i, (configuration C.support (encode C)).point i ≠ 0 := by
  intro i hi
  obtain ⟨f, hf⟩ := hnormal (fun _ => 1)
  have he := congrFun hf i
  change eval ((configuration C.support (encode C)).point i) f.val.val = 1 at he
  rw [hi] at he
  have hz : eval (0 : Fin (3 + m) → K) f.val.val = 0 := by
    simpa using homogeneous_eval_scale f.val.property (0 : Fin (3 + m) → K) (0 : K)
  exact zero_ne_one (hz.symm.trans he)

private theorem residualPiece_finrank_add_of_normalEvaluation {m p q : ℕ}
    (C : ConeConfiguration K 3 m p q) (d : ℕ)
    (h : Function.Surjective (normalEvaluation C.support (encode C) d)) :
    finrank K (C.residualPiece d) + p + N m d = N (3 + m) d := by
  let F := normalEvaluation C.support (encode C) d
  have hd := TwoGroup.rank_nullity_monoid (K := K) (U := normalForms K 3 m d)
    (C := Fin p → K) F
  have hp : finrank K (Fin p → K) = p := by simp
  rw [LinearMap.range_eq_top.mpr h, finrank_top, hp, ConeMonomialChart.normalForms_finrank] at hd
  have he := (normalKernelEquiv C.support (encode C) d).finrank_eq
  rw [configuration_encode] at he
  change finrank K (C.residualPiece d) = finrank K F.ker at he
  change p + finrank K F.ker = N (3 + m) d - N m d at hd
  have hmono : N m d ≤ N (3 + m) d := N_mono_variables d (by omega)
  omega

private theorem finrank_middle_source {V W : Type*}
    [AddCommMonoid V] [Module K V] [Module.Finite K V]
    [AddCommMonoid W] [Module K W] [Module.Finite K W] (n : ℕ) :
    finrank K ((Fin n → V) × (Fin 3 → W)) = n * finrank K V + 3 * finrank K W := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  let : Module.Free K V := Module.Free.of_divisionRing K V
  let : Module.Free K W := Module.Free.of_divisionRing K W
  have h := finrank_eq_add_of_linearEquiv (K := K) (V := (Fin n → V) × (Fin 3 → W))
    (W := Fin n → V) (U := Fin 3 → W) (LinearEquiv.refl K _)
  rw [Module.finrank_pi_fintype (R := K) (M := fun _ : Fin n => V),
    Module.finrank_pi_fintype (R := K) (M := fun _ : Fin 3 => W)] at h
  simpa [nsmul_eq_mul] using h

private theorem surjective_of_injective_of_same_finrank {V W : Type*}
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W] [Module.Finite K W]
    (f : V →ₗ[K] W) (hi : Function.Injective f) (hd : finrank K V = finrank K W) :
    Function.Surjective f := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj hi, hd]

/-- At the three-normal counts the actual middle multiplication map is
square. Full scalar rank in degree two gives the required cubic normal rank. -/
theorem quadratic_tripleNormal_middle_finrank (h : ℕ) (hmod : h % 3 = 2)
    (C : ConeConfiguration K 3 (h + 4) (2 * h + 12) ((h + 4) * (h + 5) / 3))
    (hnormal : Function.Surjective (normalEvaluation C.support (encode C) 2))
    (hscalar : Function.Surjective (representativeEvaluation K C.trace 2)) :
    finrank K ((Fin (3 + (h + 4)) → C.residualPiece 2) × (Fin 3 → C.tracePiece 2)) =
      finrank K (C.residualPiece 3) := by
  let m := h + 4
  let n := 3 + m
  let p := 2 * h + 12
  let q := (h + 4) * (h + 5) / 3
  let k₂ := finrank K (C.residualPiece 2)
  let k₃ := finrank K (C.residualPiece 3)
  let v := finrank K (C.tracePiece 2)
  have htraceEval : Function.Surjective (traceEvaluation (encode C) 2) := hscalar
  have hnormal₃ := (fullEvaluation_of_degree C.support (encode C) 2
    (encodedPoint_ne_zero_of_normalEvaluation C hnormal) hnormal htraceEval).2.2
  have hK₂ : k₂ + p + N m 2 = N n 2 :=
    residualPiece_finrank_add_of_normalEvaluation C 2 hnormal
  have hK₃ : k₃ + p + N m 3 = N n 3 :=
    residualPiece_finrank_add_of_normalEvaluation C 3 hnormal₃
  have hV := (representativeEvaluation_surjective_iff C.trace 2).mp hscalar
  rw [finrank_forms] at hV
  change v + q = N m 2 at hV
  have hcount : p + q = n * (n + 1) / 3 := by
    have hn : n = h + 7 := by dsimp [n, m]; omega
    rw [hn]
    exact tripleNormalPointCount h
  have hbalA : n * (N n 2 - (p + q)) = N n 3 - (p + q) := by
    rw [hcount]
    exact tripleNormalTraceBalance n (by dsimp [n, m]; omega) (by dsimp [n, m]; omega)
  have hbalT : m * (N m 2 - q) = N m 3 - q :=
    tripleNormalTraceBalance m (by dsimp [m]; omega) (by dsimp [m]; omega)
  have hv : v = N m 2 - q := by omega
  have hsum : k₂ + v = N n 2 - (p + q) := by omega
  have hsum3 : k₃ + (N m 3 - q) = N n 3 - (p + q) := by
    have hle := (N_pred_le m 3 (by dsimp [m]; omega) (by decide)).trans' (show q ≤ N m 2 by omega)
    change q ≤ N m 3 at hle
    omega
  have hnum : n * k₂ + 3 * v = k₃ := by
    have he : (n * k₂ + 3 * v) + m * v = k₃ + m * v := calc
      _ = n * (k₂ + v) := by dsimp only [n]; ring
      _ = N n 3 - (p + q) := by rw [hsum, hbalA]
      _ = k₃ + m * v := by rw [← hsum3, hv, hbalT]
    omega
  exact (finrank_middle_source (K := K) (V := C.residualPiece 2)
    (W := C.tracePiece 2) n).trans hnum

/-- Injectivity of the actual three-normal middle map gives bijectivity
at its square counts. -/
theorem quadratic_tripleNormal_middle_bijective (h : ℕ) (hmod : h % 3 = 2)
    (C : ConeConfiguration K 3 (h + 4) (2 * h + 12) ((h + 4) * (h + 5) / 3))
    (hnormal : Function.Surjective (normalEvaluation C.support (encode C) 2))
    (hscalar : Function.Surjective (representativeEvaluation K C.trace 2))
    (hi : Function.Injective (C.middleMultiplication 2)) :
    Function.Bijective (C.middleMultiplication 2) := by
  exact ⟨hi, surjective_of_injective_of_same_finrank (C.middleMultiplication 2) hi
    (quadratic_tripleNormal_middle_finrank h hmod C hnormal hscalar)⟩

/-- The genuine three-normal witness and the critical trace theorem give
the ambient endpoint in Appendix A.4. -/
theorem quadratic_tripleNormal_endpoint [CharZero K] (h : ℕ) (hmod : h % 3 = 2)
    (C : ConeConfiguration K 3 (h + 4) (2 * h + 12) ((h + 4) * (h + 5) / 3))
    (hnormal : Function.Surjective (normalEvaluation C.support (encode C) 2))
    (hscalar : Function.Surjective (representativeEvaluation K C.trace 2))
    (hmiddle : Function.Bijective (C.middleMultiplication 2))
    (htrace : IdealGenerationAt K (h + 3) 2 ((h + 4) * (h + 5) / 3)) :
    IdealGenerationAt K (h + 6) 2 ((h + 7) * (h + 8) / 3) := by
  let a₀ := encode C
  have hpoint := encodedPoint_ne_zero_of_normalEvaluation C hnormal
  have htraceEval : Function.Surjective (traceEvaluation a₀ 2) := by
    change Function.Surjective (representativeEvaluation K C.trace 2)
    exact hscalar
  have hmid : HasMaximalRank ((configuration C.support a₀).middleMultiplication 2) := by
    rw [show configuration C.support a₀ = C from configuration_encode C]
    exact Or.inl hmiddle.1
  have hresult := ConeA1Bridge.idealGenerationAt_of_special_middle (n := h + 3)
    (by decide : 0 < 3) (by omega) C.support a₀ 2 hpoint hnormal htraceEval hmid
    (tripleNormalTraceBalance (h + 4) (by omega) (by omega)) htrace
  have hdim : 3 + (h + 3 + 1) - 1 = h + 6 := by omega
  simpa only [hdim, tripleNormalPointCount] using hresult

end IdealGeneration.TripleNormal
