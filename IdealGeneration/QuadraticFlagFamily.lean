module

public import IdealGeneration.QuadraticUntouchedHeightLink
public import IdealGeneration.QuadraticCoreHeightPolynomial

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! An explicit infinite family of paired flags and compatible heights. -/

noncomputable section
namespace IdealGeneration.QuadraticFlagFamily
open MvPolynomial QuadraticElimination QuadraticLayerJacobian QuadraticLayerHeightOpen

variable {P J : Type*} [Fintype P]

/-- Number the distinguished pair first. -/
def baseOrder (p₀ : P) : P ≃ Fin (Fintype.card P) := by
  letI : NeZero (Fintype.card P) := ⟨Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨p₀⟩)⟩
  let e := Fintype.equivFin P
  exact e.trans (Equiv.swap (e p₀) 0)

theorem baseOrder_distinguished (p₀ : P) : (baseOrder p₀ p₀).val = 0 := by
  simp [baseOrder]

/-- Positive slopes with values `1,2` on the distinguished pair. -/
def naturalSlope (p₀ : P) (i : P × Bool) : ℕ :=
  2 * (baseOrder p₀ i.1).val + if i.2 then 2 else 1

theorem naturalSlope_injective (p₀ : P) : Function.Injective (naturalSlope p₀) := by
  rintro ⟨p, b⟩ ⟨q, c⟩ h
  have hb : b = c := by
    by_contra hn
    cases b <;> cases c <;> simp_all [naturalSlope] <;> omega
  subst c
  have hp : (baseOrder p₀ p).val = (baseOrder p₀ q).val := by
    simp [naturalSlope] at h
    omega
  exact Prod.ext ((baseOrder p₀).injective (Fin.ext hp)) rfl

variable (K : Type*) [Field K] [CharZero K] [DecidableEq J]

/-- The distinguished pair and selected layers initially reproduce the
explicit independent six-point core. -/
def parameters (p₀ : P) (layers : Bool → J) : QuadraticLiftParameters K P J where
  slope i := naturalSlope p₀ i
  distinguishedPair := p₀
  normal₀ j := if j = layers true then (1, 3) else (1, 1)
  normal₁ j := if j = layers true then (1, 4) else (1, 2)
  baseHeight _ := 1
  height₀ _ := 1
  height₁ j := if j = layers true then 3 else 2
  baseHeight_ne _ := one_ne_zero
  height₀_ne _ := one_ne_zero
  height₁_ne j := by split_ifs <;> norm_num
  determinant_ne j := by split_ifs <;> norm_num

theorem parameters_slope_injective (p₀ : P) (layers : Bool → J) :
    Function.Injective (parameters K p₀ layers).slope := by
  intro i k h
  apply naturalSlope_injective p₀
  change (naturalSlope p₀ i : K) = (naturalSlope p₀ k : K) at h
  exact_mod_cast h

@[simp] theorem parameters_slope_distinguished_false (p₀ : P) (layers : Bool → J) :
    (parameters K p₀ layers).slope (p₀, false) = 1 := by
  simp [parameters, naturalSlope, baseOrder_distinguished]

@[simp] theorem parameters_slope_distinguished_true (p₀ : P) (layers : Bool → J) :
    (parameters K p₀ layers).slope (p₀, true) = 2 := by
  simp [parameters, naturalSlope, baseOrder_distinguished]

private theorem slope_dot_ne (p₀ : P) (i : P × Bool) (m : ℕ) :
    (1 : K) + (naturalSlope p₀ i : K) * (m : K) ≠ 0 := by
  exact_mod_cast (show 1 + naturalSlope p₀ i * m ≠ 0 by omega)

theorem parameters_dot₀ (p₀ : P) (layers : Bool → J) (hle : layers false ≠ layers true)
    (i : P × Bool) (b : Bool) :
    directionDot ((parameters K p₀ layers).slope i)
      ((parameters K p₀ layers).normal₀ (layers b)) ≠ 0 := by
  cases b
  · simpa [parameters, directionDot, hle] using slope_dot_ne K p₀ i 1
  · simpa [parameters, directionDot] using slope_dot_ne K p₀ i 3

theorem parameters_dot₁ (p₀ : P) (layers : Bool → J) (hle : layers false ≠ layers true)
    (i : P × Bool) (b : Bool) :
    directionDot ((parameters K p₀ layers).slope i)
      ((parameters K p₀ layers).normal₁ (layers b)) ≠ 0 := by
  cases b
  · simpa [parameters, directionDot, hle] using slope_dot_ne K p₀ i 2
  · simpa [parameters, directionDot] using slope_dot_ne K p₀ i 4

/-- Every paired size admits actual nonzero heights for which the core cone
points are independent and all untouched layer blocks have full rank. -/
theorem exists_heights (p₀ : P) (layers : Bool → J) (hle : layers false ≠ layers true) :
    ∃ a : HeightIndex → K, ∃ ha : ∀ h, a h ≠ 0,
      (QuadraticCoreHeight.pointMatrix a).det ≠ 0 ∧
      ∀ i : P × Bool, i.1 ≠ p₀ →
        normalDet (((parameters K p₀ layers).withSelectedHeights layers a ha).gammaPair i
          (layers false)) (((parameters K p₀ layers).withSelectedHeights layers a ha).gammaPair i
          (layers true)) ≠ 0 := by
  have : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  let D := parameters K p₀ layers
  obtain ⟨a, ha, hcore, hpairs⟩ := D.exists_selected_heights layers hle
    (parameters_slope_injective K p₀ layers)
    (fun i _ => parameters_dot₀ K p₀ layers hle i)
    (fun i _ => parameters_dot₁ K p₀ layers hle i)
    (fun _ : Unit => QuadraticCoreHeight.determinant K)
    (fun _ => QuadraticCoreHeight.determinant_ne_zero K)
  exact ⟨a, ha, by simpa only [QuadraticCoreHeight.eval_determinant] using hcore (), hpairs⟩

end IdealGeneration.QuadraticFlagFamily
