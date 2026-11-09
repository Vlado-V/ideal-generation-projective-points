module

public import IdealGeneration.QuadraticInjectiveCoreBridge
public import IdealGeneration.QuadraticMiddleInjectivity

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Normal-degree elimination for the missing first lift in Appendix A.3. -/

noncomputable section
namespace IdealGeneration.QuadraticTruncatedKernel
open MvPolynomial QuadraticElimination QuadraticFlag QuadraticCoreRestriction
open QuadraticInjectiveAssembly QuadraticInjectiveCoreBridge QuadraticLiftParameters

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
variable (D : QuadraticLiftParameters K P J) (hc : Function.Injective D.slope)

local notation "T" => ((P × Bool) ⊕ J)
local notation "U" => D.firstLift
local notation "V" => D.secondLift
local notation "g₁" => firstKernelMap D.firstCorrection
local notation "g₂" => secondKernelMap D.slope D.secondCorrection
local notation "L" => LiftSpace (K := K) (H := P × Bool → K)
local notation "F" => (quadraticFlagVanishing (K := K) (P := P) (J := J))
local notation "B" => (Submodule.prod F F)

/-- The flag component of a normal-linear product is the projection of
its eliminated normal data. -/
theorem projected_eq_of_decomposition (x : ParameterOmega K P) (z : T → L) (b : B)
    (hb : quadraticPairInclusion b.val = traceKernelPair g₁ g₂ (fun j => X j) z + phi U V g₁ g₂ x) :
    D.actualProjectedPairMap hc x = b.val := by
  let w := D.actualProjectedPairMap hc x
  have hs := actualProjectedMap_spec D hc x
  have hW : w - b.val ∈ B := Submodule.sub_mem _ hs.1 b.property
  have hm : actualQuadraticPhi D x - b.val ∈ quadraticMixedImage D.slope D.firstCorrection D.secondCorrection := by
    rw [← Submodule.comap_map_eq_of_injective quadraticPairInclusion_injective
      (quadraticMixedImage D.slope D.firstCorrection D.secondCorrection)]
    change quadraticPairInclusion (actualQuadraticPhi D x - b.val) ∈
      (quadraticMixedImage D.slope D.firstCorrection D.secondCorrection).map quadraticPairInclusion
    rw [map_quadraticMixedImage, map_sub]
    change phi U V g₁ g₂ x - quadraticPairInclusion b.val ∈
      mixedImage D.slope D.firstCorrection D.secondCorrection
    rw [hb, show phi U V g₁ g₂ x - (traceKernelPair g₁ g₂ (fun j => X j) z + phi U V g₁ g₂ x) =
      -traceKernelPair g₁ g₂ (fun j => X j) z by abel, ← mixedTraceMap_range_eq_mixedImage]
    exact Submodule.neg_mem _ ⟨fun j => (z j).2, rfl⟩
  have hM : w - b.val ∈ quadraticMixedImage D.slope D.firstCorrection D.secondCorrection := by
    rw [show w - b.val = (actualQuadraticPhi D x - b.val) -
      (actualQuadraticPhi D x - w) by abel]
    exact Submodule.sub_mem _ hm hs.2
  have hdis := mixedImage_disjoint_flagVanishing D.slope D.firstCorrection D.secondCorrection hc
  apply sub_eq_zero.mp
  apply quadraticPairInclusion_injective
  rw [map_zero]
  exact Submodule.disjoint_def.mp hdis _ (by rw [← map_quadraticMixedImage]; exact ⟨_,hM,rfl⟩) hW

/-- Vanishing of the first lift coefficient in all source quadrics gives
the missing-generator constraint on the eliminated normal data. -/
theorem missingFirstLiftCoefficient_eq_zero_of_product (x y : L) (z : T → L) (b : B)
    (hy : y.1 0 = 0) (hz : ∀ j, (z j).1 0 = 0)
    (hp : middleMultiplication U V g₁ g₂ ((x,y),z) = normalPairMap (quadraticPairInclusion b.val)) :
    ∃ w : ParameterOmega K P, w.val = (x,y) ∧
      missingFirstLiftCoefficient U g₁ w = 0 ∧ D.actualProjectedPairMap hc w = b.val := by
  have hinj : Function.Injective (algebraMap K (MvPolynomial T K)) := by
    simpa only [MvPolynomial.algebraMap_eq] using MvPolynomial.C_injective (σ := T) (R := K)
  rw [middleMultiplication_apply, normalPairMap_apply] at hp
  obtain ⟨w, hw, hdec⟩ := normalLinear_product_decomposition hinj U V g₁ g₂ (fun j => X j)
    z x y (quadraticPairInclusion b.val).1 (quadraticPairInclusion b.val).2 hp
  obtain ⟨_, h0, _, _⟩ := normalLinear_product_constraints hinj U V g₁ g₂ (fun j => X j)
    z x y (quadraticPairInclusion b.val).1 (quadraticPairInclusion b.val).2 hp
  have hz0 : traceNormalCoefficient (fun j : T => (X j : MvPolynomial T K)) z 0 = 0 := by
    simp [traceNormalCoefficient, hz]
  rw [hz0, zero_add] at h0
  refine ⟨w, hw, ?_, projected_eq_of_decomposition D hc w z b (by simpa only [Prod.mk.eta] using hdec)⟩
  rw [missingFirstLiftCoefficient_apply, hw]
  refine Prod.ext ?_ hy
  change -lowerPart U g₁ x = 0
  rw [h0, neg_zero]

/-- With the first generator omitted, the core and first-layer pair probes
force every normal-linear product with these zero values to vanish. -/
theorem truncatedProduct_eq_zero (e : Fin 2 ↪ J)
    (hi : Function.Injective (fixedFirstLayerConstraintProbeMap D e hc))
    (x y : L) (z : T → L) (b : B)
    (hy : y.1 0 = 0) (hz : ∀ j, (z j).1 0 = 0)
    (hp : middleMultiplication U V g₁ g₂ ((x,y),z) = normalPairMap (quadraticPairInclusion b.val))
    (hcore : (eval (embeddedCoreTProbe D e) b.val.1.val,
      eval (embeddedCoreTProbe D e) b.val.2.val) = 0)
    (hpairs : ∀ p : {p : P // p ≠ D.distinguishedPair},
      (eval (pairProbe p.val (e 0)) b.val.1.val, eval (pairProbe p.val (e 0)) b.val.2.val) = 0) :
    b = 0 := by
  obtain ⟨w, _, hw, hb⟩ := missingFirstLiftCoefficient_eq_zero_of_product D hc x y z b hy hz hp
  have hprobe (point : T → K) :
      projectedProbe D hc point w = (eval point b.val.1.val, eval point b.val.2.val) := by
    simp only [projectedProbe_apply, hb]
  have hzero : fixedFirstLayerConstraintProbeMap D e hc w = 0 := by
    apply Prod.ext hw
    apply Prod.ext
    · exact (hprobe _).trans hcore
    · funext p
      exact (hprobe _).trans (hpairs p)
  have hw0 : w = 0 := hi (hzero.trans (map_zero _).symm)
  apply Subtype.ext
  rw [← hb, hw0, map_zero]
  exact Submodule.coe_zero.symm

end IdealGeneration.QuadraticTruncatedKernel
