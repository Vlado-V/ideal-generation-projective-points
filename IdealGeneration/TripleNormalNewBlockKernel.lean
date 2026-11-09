module

public import IdealGeneration.TripleNormalNewBaseRank
public import IdealGeneration.TripleNormalSourceRestriction
public import IdealGeneration.TripleNormalNewLayerSourceCoordinates

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual new source block is detected by the appended trace rows. -/

noncomputable section
namespace IdealGeneration.TripleNormal

open MvPolynomial SupportedQuadrics

variable {K : Type*} [Field K] {h p q r : ℕ}

private theorem sum_single_mul {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (f : I → K) :
    (∑ j, (Pi.single i (1 : K) : I → K) j * f j) = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private theorem sum_append_single_mul (b : Fin 3) (f : Fin (h + 3) → K) :
    (∑ i, Fin.append (0 : Fin h → K) (Pi.single b 1) i * f i) =
      f (b.natAdd h) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    Fin.append_right]
  exact sum_single_mul b (fun i => f (i.natAdd h))

/-- On its own coordinate point a new motion has zero diagonal contribution. -/
theorem newBaseValue_coordinate (ω : K) (t : Fin h → K) (v : Fin 3 → K)
    (hω : IsPrimitiveRoot ω 3) (u : Fin 3 → Fin 3 → K)
    (ρ : Fin (h + 3 + 4) → Fin (h + 3) → K) (b : Fin 3) :
    newBaseValue ω t v u ρ (Fin.append 0 (Pi.single b 1)) 0 =
      ρ ((b.natAdd h).castAdd 4) (b.natAdd h) := by
  simp only [newBaseValue, Fin.append_right, sum_append_single_mul, sum_single_mul,
    newMotionQuadric, baseLiftCoefficient_motionQuadratic_diagonal ω (v b) hω,
    Pi.zero_apply, neg_zero, zero_add]
  simp [conicVector]

variable (C : ConeConfiguration K 3 (h + 4) p q)
  (free : Fin r × Fin (h + 3) → K) (ζnew : Fin 4 → K) (nnew : Fin 3 → Fin 2 → Fin 3 → K)
  (ω : K) (t : Fin h → K) (v : Fin 3 → K) (n : Layer.Normals K) (ζ : Layer.Heights K)

local notation "Cnew" => supportedExtension C free ζnew nnew

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The free base rank and the explicit layer blocks detect every new
coefficient of an actual source vector whose restriction is zero. -/
theorem supportedExtension_newBlock_zero
    (oldPoints : PointPattern C ω t n ζ (Layer.baseSupport K h))
    (newPoints : PointPattern Cnew ω (Fin.append t v) n ζ (Layer.baseSupport K (h + 3)))
    (hω : IsPrimitiveRoot ω 3) (ht : ∀ i, t i ≠ 0) (htv : ∀ i, Fin.append t v i ≠ 0)
    (hdet : ∀ j, (Layer.normalMatrix n j).det ≠ 0) (hζ : ∀ j ν, ζ j ν ≠ 0) (hh : 6 ≤ h)
    (hv : Function.Injective v) (hζnew : ∀ j, ζnew j ≠ 0)
    (hheight : ∀ i, (Cnew).height i ≠ 0) (hbase : NewBaseRank ω t v free)
    (x : EvaluationSource Cnew)
    (hrestrict : supportedExtensionEvaluationSourceRestriction C free ζnew nnew x = 0)
    (heval : allowedEvaluationMap Cnew
      (pureLift Cnew ω (Fin.append t v) n ζ (Layer.baseSupport K (h + 3)) newPoints hω htv hdet hζ)
      (pureRestrict_pureLift Cnew ω (Fin.append t v) n ζ (Layer.baseSupport K (h + 3))
        newPoints hω htv hdet hζ) hheight x = 0) :
    x = 0 := by
  let τ := Fin.append t v
  let b := Layer.baseSupport K (h + 3)
  let E := residualEquiv Cnew ω τ n ζ b newPoints hω htv hdet hζ
  let hE := residualEquiv_fst Cnew ω τ n ζ b newPoints hω htv hdet hζ
  let H := mixedEquiv Cnew ω τ n ζ b newPoints hω htv hdet hζ
  let L := pureLift Cnew ω τ n ζ b newPoints hω htv hdet hζ
  let M := mixedKernelCoordinatesEquiv Cnew E hE
  let z := evaluationSourceCoordinatesEquiv Cnew E hE x
  let u : Fin 3 → Fin 3 → K := fun i a => z.1.2 a (i.natAdd h)
  let ρ : Fin (h + 3 + 4) → Fin (h + 3) → K := z.2
  have hcoords := supportedEvaluationSourceRestriction_coordinates C free ζnew nnew ω t v n ζ
    oldPoints newPoints hω ht htv hdet hζ hh x
  let Eold := evaluationSourceCoordinatesEquiv C
    (residualEquiv C ω t n ζ (Layer.baseSupport K h) oldPoints hω ht hdet hζ)
    (residualEquiv_fst C ω t n ζ (Layer.baseSupport K h) oldPoints hω ht hdet hζ)
  change Eold (supportedExtensionEvaluationSourceRestriction C free ζnew nnew x) =
    sourceCoordinateRestriction h z at hcoords
  rw [hrestrict, Eold.map_zero] at hcoords
  have hz : sourceCoordinateRestriction h z = 0 := hcoords.symm
  have hpure : z.1.1 = 0 := congrArg (fun w : SourceCoordinates K h => w.1.1) hz
  have hmotions (a : Fin 3) (i : Fin h) : z.1.2 a (i.castAdd 3) = 0 :=
    congrArg (fun w : SourceCoordinates K h => w.1.2 a i) hz
  have hold (j : Fin (h + 4)) (i : Fin h) : ρ (oldTraceIndex h j) (i.castAdd 3) = 0 :=
    congrArg (fun w : SourceCoordinates K h => w.2 j i) hz
  have hH (γ : Fin (h + 3) → K) : E (H γ).val = (0, γ) :=
    (liftEquiv Cnew ω τ n ζ b newPoints hω htv hdet hζ).symm_apply_apply (0, γ)
  have hmixed (γ : Fin (h + 3) → K) : M (H γ) = γ := congrArg Prod.snd (hH γ)
  have hη : x.1 = newMotionOmega Cnew ω t v n ζ newPoints hω htv hdet hζ u := by
    apply Subtype.ext
    funext a
    apply E.injective
    change E (x.1.val a) = E (H (Fin.append 0 (fun i => u i a))).val
    rw [hH]
    apply Prod.ext
    · exact congrArg (fun w : PureOmega K => w.val a) hpure
    · change z.1.2 a = Fin.append 0 (fun i => u i a)
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left, Pi.zero_apply] using hmotions a j
      · simp only [Fin.append_right, u]
  have hρ : x.2 = fun j => H (ρ j) := by
    funext j
    apply M.injective
    change ρ j = M (H (ρ j))
    rw [hmixed]
  have hx : x = (newMotionOmega Cnew ω t v n ζ newPoints hω htv hdet hζ u,
      fun j => H (ρ j)) := Prod.ext hη hρ
  have hzero (a : Fin 3) (j : Fin (q + (3 + (r + 4)))) :
      eval ((Cnew).trace j) ((reducedCoefficient Cnew L x) a).val = 0 :=
    congrArg (fun w : AllowedValues Cnew => w.val a j) heval
  have hformula (y : Fin (h + 3) → K) (a : Fin 3) :
      eval (Fin.append y 0) ((reducedCoefficient Cnew L x) a).val =
        newBaseValue ω t v u ρ y a := by
    rw [hx]
    exact eval_reducedCoefficient_newMotion_base Cnew ω t v n ζ newPoints hω htv hdet hζ hh u ρ y a
  have hdiag (i : Fin 3) : ρ ((i.natAdd h).castAdd 4) (i.natAdd h) = 0 := by
    have he := hzero 0 ((i.castAdd (r + 4)).natAdd q)
    rw [supportedExtension_trace_coordinate] at he
    change eval (Fin.append (Fin.append (0 : Fin h → K) (Pi.single i 1)) 0)
      ((reducedCoefficient Cnew L x) 0).val = 0 at he
    rwa [hformula, newBaseValue_coordinate ω t v hω] at he
  have hfree (i : Fin r) (a : Fin 3) :
      newBaseValue ω t v u ρ (fun j => free (i, j)) a = 0 := by
    have he := hzero a (((i.castAdd 4).natAdd 3).natAdd q)
    rw [supportedExtension_trace_free] at he
    change eval (Fin.append (fun j => free (i, j)) 0)
      ((reducedCoefficient Cnew L x) a).val = 0 at he
    rwa [hformula] at he
  obtain ⟨hu, hrows⟩ := hbase u ρ (fun i j => by
    have he : oldTraceIndex h (i.castAdd 4) = (i.castAdd 3).castAdd 4 := by
      simp only [oldTraceIndex, Fin.addCases_left]
      rfl
    simpa only [he] using hold (i.castAdd 4) j) hdiag hfree
  have hηzero : x.1 = 0 := by
    rw [hη, hu]
    apply Subtype.ext
    funext a
    change (H (Fin.append 0 (fun i => (0 : Fin 3 → Fin 3 → K) i a))).val = 0
    have hz' : Fin.append (0 : Fin h → K) (fun i => (0 : Fin 3 → Fin 3 → K) i a) = 0 := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    rw [hz', map_zero]
    rfl
  let c : Fin 4 → Fin 3 → K := fun j i => ρ (NewLayerBlock.layerVariable h j) (i.natAdd h)
  let S := NewLayerBlock.layerMixedSource Cnew ω t v n ζ newPoints hω htv hdet hζ
  have hS : x.2 = S c := by
    funext i
    apply M.injective
    change ρ i = M (S c i)
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [NewLayerBlock.layerMixedSource_coordinates_base Cnew ω t v n ζ newPoints hω htv hdet hζ]
      exact hrows j
    · change ρ (NewLayerBlock.layerVariable h j) = M (S c (NewLayerBlock.layerVariable h j))
      have hl : M (S c (NewLayerBlock.layerVariable h j)) =
          Fin.append (0 : Fin h → K) (c j) :=
        NewLayerBlock.layerMixedSource_coordinates_layer Cnew ω t v n ζ newPoints
          hω htv hdet hζ c j
      rw [hl]
      funext k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp only [Fin.append_left, Pi.zero_apply]
        have he : oldTraceIndex h (j.natAdd h) = j.natAdd (h + 3) := by
          simp only [oldTraceIndex, Fin.addCases_right]
          rfl
        simpa only [he, NewLayerBlock.layerVariable] using hold (j.natAdd h) i
      · simp only [Fin.append_right, c, NewLayerBlock.layerVariable]
  have hSource : x = (0, S c) := Prod.ext hηzero hS
  have hReduced : reducedCoefficient Cnew L x = NewLayerBlock.vectorQuadratic h v c := by
    rw [hSource]
    exact NewLayerBlock.reducedCoefficient_layerMixedSource Cnew ω t v n ζ newPoints
      hω htv hdet hζ hh c L
  have hLayer : NewLayerBlock.layerBlock h v ζnew c = NewLayerBlock.layerBlock h v ζnew 0 := by
    rw [map_zero]
    funext j a
    change eval (extensionLayer h ζnew j) ((NewLayerBlock.vectorQuadratic h v c) a).val = 0
    have he := hzero a (((j.natAdd r).natAdd 3).natAdd q)
    rwa [supportedExtension_trace_layer, hReduced] at he
  have hc : c = 0 := (NewLayerBlock.layerBlock_bijective h v ζnew hv hζnew).1 hLayer
  rw [hSource, hc, map_zero]
  rfl

end IdealGeneration.TripleNormal
