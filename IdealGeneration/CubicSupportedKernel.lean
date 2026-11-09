module

public import IdealGeneration.CubicSupportedCoordinates

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The local solves give all coefficient cubics in the supported cone kernel. -/

namespace IdealGeneration.CubicSupported

section TwoNormals

variable {K : Type*} [Field K]

private theorem eq_of_normal_and_second {a b : Fin 2 → K} (t : K)
    (hn : normalLinear a 1 t = normalLinear b 1 t) (hsecond : a 1 = b 1) : a = b := by
  simp only [normalLinear, mul_one, hsecond] at hn
  have hfirst := add_right_cancel hn
  funext k
  fin_cases k
  · exact hfirst
  · exact hsecond

private theorem eq_of_two_normals {a b : Fin 2 → K} (t₀ t₁ : K) (ht : t₀ ≠ t₁)
    (h₀ : normalLinear a 1 t₀ = normalLinear b 1 t₀)
    (h₁ : normalLinear a 1 t₁ = normalLinear b 1 t₁) : a = b := by
  have hprod : (t₁ - t₀) * (a 1 - b 1) = 0 := by
    unfold normalLinear at h₀ h₁
    linear_combination h₁ - h₀
  have hs := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr ht.symm))
  exact eq_of_normal_and_second t₀ h₀ hs

end TwoNormals

namespace Parameters

open MvPolynomial
variable {K : Type*} [Field K] {m : ℕ} (P : Parameters K m)

private theorem kernel_diagonal_normal (u : P.coefficientKernel) (i : Fin m) (d : Fin 2) :
    normalLinear (u.val.2.2.1 i) 1 (P.vertexSlope i d) =
      normalLinear (P.diagonalLift u.val.1 u.val.2.1 i) 1 (P.vertexSlope i d) := by
  have h := (P.mem_coefficientKernel u.val).1 u.property (.inl (i, d))
  change eval (P.vertexPoint i d) (polynomial u.val.1 u.val.2.1 u.val.2.2.1 u.val.2.2.2) = 0 at h
  rw [eval_polynomial] at h
  simp only [vertexPoint_normal_zero, vertexPoint_normal_one, vertexPoint_trace] at h
  rw [cubicValue_vertex] at h
  change normalCubic u.val.1 1 (P.vertexSlope i d) +
    P.vertexHeight i d * normalQuadratic (u.val.2.1 i) 1 (P.vertexSlope i d) +
    (P.vertexHeight i d) ^ 2 * normalLinear (u.val.2.2.1 i) 1 (P.vertexSlope i d) = 0 at h
  have hlift := P.diagonalLift_constraint u.val.1 u.val.2.1 i d
  have hp : (P.vertexHeight i d) ^ 2 *
      (normalLinear (u.val.2.2.1 i) 1 (P.vertexSlope i d) -
        normalLinear (P.diagonalLift u.val.1 u.val.2.1 i) 1 (P.vertexSlope i d)) = 0 := by
    linear_combination h - hlift
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ (P.vertexHeight_ne i d)))

/-- Every kernel cubic has the same diagonal solve for its top coefficients. -/
theorem kernel_diagonal_eq (u : P.coefficientKernel) :
    u.val.2.2.1 = P.diagonalLift u.val.1 u.val.2.1 := by
  funext i
  exact eq_of_two_normals (P.vertexSlope i 0) (P.vertexSlope i 1) (P.vertexSlope_ne i)
    (P.kernel_diagonal_normal u i 0) (P.kernel_diagonal_normal u i 1)

private theorem kernel_offDiagonal_normal (u : P.coefficientKernel)
    (z : P.SingleEdge → K) (e : Edge m) (d : Fin 2) (hd : P.EdgeSlot e d) :
    normalLinear (u.val.2.2.2 e) 1 (P.edgeSlope e d) =
      normalLinear (P.offDiagonalLift u.val.1 u.val.2.1 z e) 1 (P.edgeSlope e d) := by
  have h := (P.mem_coefficientKernel u.val).1 u.property (.inr ⟨(e, d), hd⟩)
  change eval (P.edgePoint e d) (polynomial u.val.1 u.val.2.1 u.val.2.2.1 u.val.2.2.2) = 0 at h
  rw [eval_polynomial] at h
  simp only [edgePoint_normal_zero, edgePoint_normal_one, edgePoint_trace] at h
  rw [cubicValue_edge] at h
  change normalCubic u.val.1 1 (P.edgeSlope e d) +
    P.edgeHeight e d * (normalQuadratic (u.val.2.1 e.val.1) 1 (P.edgeSlope e d) +
      P.edgeLambda e * normalQuadratic (u.val.2.1 e.val.2) 1 (P.edgeSlope e d)) +
    (P.edgeHeight e d) ^ 2 *
      (normalLinear (u.val.2.2.1 e.val.1) 1 (P.edgeSlope e d) +
        P.edgeLambda e * normalLinear (u.val.2.2.2 e) 1 (P.edgeSlope e d) +
        (P.edgeLambda e) ^ 2 * normalLinear (u.val.2.2.1 e.val.2) 1 (P.edgeSlope e d)) = 0 at h
  rw [P.kernel_diagonal_eq u] at h
  have hlift := P.offDiagonalLift_constraint u.val.1 u.val.2.1 z e d hd
  have hp : (P.edgeHeight e d) ^ 2 * P.edgeLambda e *
      (normalLinear (u.val.2.2.2 e) 1 (P.edgeSlope e d) -
        normalLinear (P.offDiagonalLift u.val.1 u.val.2.1 z e) 1 (P.edgeSlope e d)) = 0 := by
    linear_combination h - hlift
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left
    (mul_ne_zero (pow_ne_zero _ (P.edgeHeight_ne e d)) (P.edgeLambda_ne e)))

/-- The negative `t` coefficient on a single edge records its free graph coordinate. -/
def freeCoefficients (u : P.coefficientKernel) (e : P.SingleEdge) : K :=
  -u.val.2.2.2 e.val 1

/-- Every increasing-edge coefficient is the local solve with the recovered free coordinate. -/
theorem kernel_offDiagonal_eq (u : P.coefficientKernel) :
    u.val.2.2.2 = P.offDiagonalLift u.val.1 u.val.2.1 (P.freeCoefficients u) := by
  funext e
  by_cases hs : P.single e = true
  · apply eq_of_normal_and_second (P.edgeSlope e 0)
    · exact P.kernel_offDiagonal_normal u (P.freeCoefficients u) e 0 (Or.inr rfl)
    · simp [offDiagonalLift, hs, freeCoefficients]
  · have hf : P.single e = false := Bool.eq_false_of_not_eq_true hs
    exact eq_of_two_normals (P.edgeSlope e 0) (P.edgeSlope e 1) (P.edgeSlope_ne e hf)
      (P.kernel_offDiagonal_normal u (P.freeCoefficients u) e 0 (Or.inl hf))
      (P.kernel_offDiagonal_normal u (P.freeCoefficients u) e 1 (Or.inl hf))

/-- Recover the four normal-cubic coefficients, the mixed quadratics and the single-edge coordinates. -/
def kernelCoordinates : P.coefficientKernel →ₗ[K]
    ((Fin 4 → K) × (Fin m → Fin 3 → K) × (P.SingleEdge → K)) where
  toFun u := (u.val.1, u.val.2.1, P.freeCoefficients u)
  map_add' u v := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext e
    change -(u.val.2.2.2 e.val 1 + v.val.2.2.2 e.val 1) = _
    change _ = -u.val.2.2.2 e.val 1 + -v.val.2.2.2 e.val 1
    ring
  map_smul' r u := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext e
    change -(r * u.val.2.2.2 e.val 1) = r * (-u.val.2.2.2 e.val 1)
    ring

private theorem kernelCoordinates_injective : Function.Injective P.kernelCoordinates := by
  intro u v h
  change (u.val.1, u.val.2.1, P.freeCoefficients u) =
    (v.val.1, v.val.2.1, P.freeCoefficients v) at h
  have hC := congrArg Prod.fst h
  have hB := congrArg (fun x => x.2.1) h
  have hz := congrArg (fun x => x.2.2) h
  change u.val.1 = v.val.1 at hC
  change u.val.2.1 = v.val.2.1 at hB
  change P.freeCoefficients u = P.freeCoefficients v at hz
  apply Subtype.ext
  refine Prod.ext hC (Prod.ext hB (Prod.ext ?_ ?_))
  · rw [P.kernel_diagonal_eq u, P.kernel_diagonal_eq v, hC, hB]
  · rw [P.kernel_offDiagonal_eq u, P.kernel_offDiagonal_eq v, hC, hB, hz]

private theorem kernelCoordinates_surjective : Function.Surjective P.kernelCoordinates := by
  rintro ⟨C, B, z⟩
  refine ⟨P.coefficientLift C B z, Prod.ext rfl (Prod.ext rfl ?_)⟩
  funext e
  change -P.offDiagonalLift C B z e.val 1 = z e
  simp [offDiagonalLift, e.property]

/-- The supported cone kernel is parametrized by the top coefficients and the single edges. -/
noncomputable def kernelCoordinatesEquiv : P.coefficientKernel ≃ₗ[K]
    ((Fin 4 → K) × (Fin m → Fin 3 → K) × (P.SingleEdge → K)) :=
  LinearEquiv.ofBijective P.kernelCoordinates
    ⟨P.kernelCoordinates_injective, P.kernelCoordinates_surjective⟩

/-- The supported cubic kernel has the dimension in Lemma B.3. -/
theorem finrank_coefficientKernel : Module.finrank K P.coefficientKernel =
    4 + 3 * m + Fintype.card P.SingleEdge := by
  rw [P.kernelCoordinatesEquiv.finrank_eq]
  simp [Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm, Nat.add_assoc]

end Parameters
end IdealGeneration.CubicSupported
