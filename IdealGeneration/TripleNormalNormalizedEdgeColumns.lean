module

public import IdealGeneration.TripleNormalEdgeOrder
public import IdealGeneration.TripleNormalRootBlock

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The coefficient columns of the edge model after changing coordinates in the root block. -/

noncomputable section
namespace IdealGeneration.TripleNormal.NormalizedEdgeColumns

open EdgeOrder
open scoped Matrix

variable {K : Type*} [Field K] {N : ℕ}

abbrev PlaneEdge (N : ℕ) := NonrootEdge N ⊕ TriangleEdge

abbrev RawInput (K : Type*) (N : ℕ) :=
  (Fin 3 → Fin 3 → K) × (Edge N → Fin 2 → K)

abbrev NormalizedInput (K : Type*) (N : ℕ) :=
  (PlaneEdge N → Fin 2 → K) × RootBlockOutput K

abbrev Output (K : Type*) (N : ℕ) := Edge N → Fin 3 → K

def planeEmbed : PlaneEdge N → Edge N := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)

def rootEdge (r b : Fin 3) : Edge N := .inr (.inr (r, b))

@[simp] theorem planeEmbed_nonroot (e : NonrootEdge N) :
    planeEmbed (.inl e) = Sum.inl e := rfl

@[simp] theorem planeEmbed_triangle (e : TriangleEdge) :
    planeEmbed (N := N) (.inr e) = Sum.inr (.inl e) := rfl

theorem planeEmbed_injective : Function.Injective (planeEmbed (N := N)) := by
  intro e f h
  cases e <;> cases f <;> simp_all [planeEmbed]

def rootParameters (t : Fin (N + 3) → K) : Fin 3 → K := fun r => t (r.natAdd N)

/-- The two conic parameters at the endpoints of an edge. -/
def endpointParameter (t : Fin (N + 3) → K) (v : Fin 3 → K) : Edge N → Fin 2 → K :=
  Sum.elim
    (fun e => ![t (e.1.castAdd 3), v e.2])
    (Sum.elim
      (fun e => ![v e.val.1, v e.val.2])
      (fun e => ![rootParameters t e.1, v e.2]))

/-- The two vectors that can be contributed directly at an edge. -/
def endpointVector (t : Fin (N + 3) → K) (v : Fin 3 → K) (e : Edge N) (k : Fin 2) :
    Fin 3 → K := conicVector (endpointParameter t v e k)

theorem endpointVector_independent (t : Fin (N + 3) → K) (v : Fin 3 → K)
    (e : Edge N) (h : endpointParameter t v e 0 ≠ endpointParameter t v e 1) :
    LinearIndependent K (endpointVector t v e) := by
  have he : endpointVector t v e =
      ![conicVector (endpointParameter t v e 0), conicVector (endpointParameter t v e 1)] := by
    funext k
    fin_cases k <;> simp [endpointVector]
  rw [he]
  exact conicVector_pair_independent _ _ h

theorem endpointVector_orthogonal (t : Fin (N + 3) → K) (v : Fin 3 → K)
    (e : Edge N) (k : Fin 2) :
    chordNormal (endpointParameter t v e 0) (endpointParameter t v e 1) ⬝ᵥ endpointVector t v e k = 0 := by
  fin_cases k
  · exact chordNormal_dot_conic_left _ _
  · exact chordNormal_dot_conic_right _ _

private def motionLift (ω s b : K) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
  (baseLiftCoefficient ω s).comp ((mulForm (Layer.normalForm (conicVector b))).comp
    Layer.normalForm)

private theorem motionLift_apply (ω s b : K) (u : Fin 3 → K) :
    motionLift ω s b u = baseLiftCoefficient ω s (motionQuadratic u (conicVector b)) := by
  change baseLiftCoefficient ω s
    (mulForm (Layer.normalForm (conicVector b)) (Layer.normalForm u)) = _
  exact congrArg (baseLiftCoefficient ω s) (Subtype.ext
    (mul_comm (Layer.normalForm (conicVector b)).val (Layer.normalForm u).val))

private def edgeCorrection (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K) :
    Edge N → (Fin 3 → Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
  Sum.elim
    (fun e => (motionLift ω (t (e.1.castAdd 3)) (v e.2)).comp (LinearMap.proj e.2))
    (Sum.elim
      (fun e => (motionLift ω (v e.val.1) (v e.val.2)).comp (LinearMap.proj e.val.2) +
        (motionLift ω (v e.val.2) (v e.val.1)).comp (LinearMap.proj e.val.1))
      (fun e => (motionLift ω (rootParameters t e.1) (v e.2)).comp (LinearMap.proj e.2)))

/-- The unnormalized edge vectors, including the contributions from the local lifts. -/
def rawCoefficient (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K) :
    RawInput K N →ₗ[K] Output K N where
  toFun f e := f.2 e 0 • endpointVector t v e 0 + f.2 e 1 • endpointVector t v e 1 -
    edgeCorrection ω t v e f.1
  map_add' f g := by
    funext e
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, map_add]
    abel
  map_smul' a f := by
    funext e
    simp [smul_add, smul_sub, smul_smul, smul_eq_mul]

theorem rawCoefficient_nonroot (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K)
    (f : RawInput K N) (i : Fin N) (b : Fin 3) :
    rawCoefficient ω t v f (.inl (i, b)) =
      f.2 (.inl (i, b)) 0 • conicVector (t (i.castAdd 3)) +
      f.2 (.inl (i, b)) 1 • conicVector (v b) -
      baseLiftCoefficient ω (t (i.castAdd 3)) (motionQuadratic (f.1 b) (conicVector (v b))) := by
  change _ - motionLift ω (t (i.castAdd 3)) (v b) (f.1 b) = _
  rw [motionLift_apply]
  simp [endpointVector, endpointParameter]

theorem rawCoefficient_triangle (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K)
    (f : RawInput K N) (e : TriangleEdge) :
    rawCoefficient ω t v f (.inr (.inl e)) =
      f.2 (.inr (.inl e)) 0 • conicVector (v e.val.1) +
      f.2 (.inr (.inl e)) 1 • conicVector (v e.val.2) -
      (baseLiftCoefficient ω (v e.val.1) (motionQuadratic (f.1 e.val.2) (conicVector (v e.val.2))) +
      baseLiftCoefficient ω (v e.val.2) (motionQuadratic (f.1 e.val.1) (conicVector (v e.val.1)))) := by
  change _ - (motionLift ω (v e.val.1) (v e.val.2) (f.1 e.val.2) +
    motionLift ω (v e.val.2) (v e.val.1) (f.1 e.val.1)) = _
  rw [motionLift_apply, motionLift_apply]
  simp [endpointVector, endpointParameter]

theorem rawCoefficient_root (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K)
    (f : RawInput K N) (r b : Fin 3) :
    rawCoefficient ω t v f (rootEdge r b) =
      rootBlockMap ω (rootParameters t) v (f.1, fun r b => f.2 (rootEdge r b)) r b := by
  change _ - motionLift ω (rootParameters t r) (v b) (f.1 b) = _
  rw [motionLift_apply, rootBlockMap_apply]
  simp [endpointVector, endpointParameter, rootEdge]

section Normalization

variable [CharZero K]
variable (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K)
variable (hω : IsPrimitiveRoot ω 3) (hroots : ∀ r, rootParameters t r ≠ 0)
  (hinj : Function.Injective (rootParameters t))
  (hq : ∀ r b, chordFactor (rootParameters t r) (v b) ≠ 0)

local notation "R" => rootBlockEquiv ω (rootParameters t) v hω hroots hinj hq

/-- Root data recovers the motions and root pairs. Plane pairs retain their coordinates. -/
def recover : NormalizedInput K N →ₗ[K] RawInput K N where
  toFun x :=
    let z := (R).symm x.2
    (z.1, Sum.elim (fun e => x.1 (.inl e))
      (Sum.elim (fun e => x.1 (.inr e)) (fun e => z.2 e.1 e.2)))
  map_add' x y := by
    apply Prod.ext
    · change ((R).symm (x.2 + y.2)).1 = ((R).symm x.2).1 + ((R).symm y.2).1
      rw [map_add, Prod.fst_add]
    · funext e
      rcases e with e | (e | e)
      · rfl
      · rfl
      · change ((R).symm (x.2 + y.2)).2 e.1 e.2 = ((R).symm x.2).2 e.1 e.2 + ((R).symm y.2).2 e.1 e.2
        rw [map_add, Prod.snd_add, Pi.add_apply, Pi.add_apply]
  map_smul' a x := by
    apply Prod.ext
    · change ((R).symm (a • x.2)).1 = a • ((R).symm x.2).1
      rw [map_smul]
      rfl
    · funext e
      rcases e with e | (e | e)
      · rfl
      · rfl
      · change ((R).symm (a • x.2)).2 e.1 e.2 = a • ((R).symm x.2).2 e.1 e.2
        rw [map_smul]
        rfl

@[simp] theorem recover_motions (x : NormalizedInput K N) :
    (recover ω t v hω hroots hinj hq x).1 = ((R).symm x.2).1 := rfl

@[simp] theorem recover_plane (x : NormalizedInput K N) (e : PlaneEdge N) :
    (recover ω t v hω hroots hinj hq x).2 (planeEmbed e) = x.1 e := by
  cases e <;> rfl

@[simp] theorem recover_root (x : NormalizedInput K N) (r b : Fin 3) :
    (recover ω t v hω hroots hinj hq x).2 (rootEdge r b) = ((R).symm x.2).2 r b := rfl

theorem recover_bijective : Function.Bijective (recover ω t v hω hroots hinj hq) := by
  constructor
  · intro x y hxy
    apply Prod.ext
    · funext e
      simpa only [recover_plane] using congrArg (fun f : RawInput K N => f.2 (planeEmbed e)) hxy
    · apply (R).symm.injective
      apply Prod.ext
      · simpa only [recover_motions] using congrArg Prod.fst hxy
      · funext r b
        simpa only [recover_root] using congrArg (fun f : RawInput K N => f.2 (rootEdge r b)) hxy
  · intro f
    refine ⟨(fun e => f.2 (planeEmbed e), R (f.1, fun r b => f.2 (rootEdge r b))), ?_⟩
    apply Prod.ext
    · simp
    · funext e
      rcases e with e | (e | ⟨r, b⟩)
      · exact recover_plane ω t v hω hroots hinj hq _ (.inl e)
      · exact recover_plane ω t v hω hroots hinj hq _ (.inr e)
      · change (recover ω t v hω hroots hinj hq _).2 (rootEdge r b) = f.2 (rootEdge r b)
        rw [recover_root, LinearEquiv.symm_apply_apply]

/-- Normalization is a change of coordinates on all the input columns. -/
def recoverEquiv : NormalizedInput K N ≃ₗ[K] RawInput K N :=
  LinearEquiv.ofBijective (recover ω t v hω hroots hinj hq)
    (recover_bijective ω t v hω hroots hinj hq)

@[simp] theorem recoverEquiv_apply (x : NormalizedInput K N) :
    recoverEquiv ω t v hω hroots hinj hq x = recover ω t v hω hroots hinj hq x := rfl

def normalizedCoefficient : NormalizedInput K N →ₗ[K] Output K N :=
  (rawCoefficient ω t v).comp (recover ω t v hω hroots hinj hq)

@[simp] theorem normalizedCoefficient_root (x : NormalizedInput K N) (r b : Fin 3) :
    normalizedCoefficient ω t v hω hroots hinj hq x (rootEdge r b) = x.2 r b := by
  rw [normalizedCoefficient, LinearMap.comp_apply, rawCoefficient_root]
  change R ((R).symm x.2) r b = x.2 r b
  rw [LinearEquiv.apply_symm_apply]

theorem normalizedCoefficient_plane_zeroRoot (p : PlaneEdge N → Fin 2 → K) (e : PlaneEdge N) :
    normalizedCoefficient ω t v hω hroots hinj hq (p, 0) (planeEmbed e) =
      p e 0 • endpointVector t v (planeEmbed e) 0 + p e 1 • endpointVector t v (planeEmbed e) 1 := by
  let f := recover ω t v hω hroots hinj hq (p, 0)
  change f.2 (planeEmbed e) 0 • endpointVector t v (planeEmbed e) 0 +
    f.2 (planeEmbed e) 1 • endpointVector t v (planeEmbed e) 1 -
    edgeCorrection ω t v (planeEmbed e) f.1 = _
  have hp : f.2 (planeEmbed e) = p e := recover_plane ω t v hω hroots hinj hq (p, 0) e
  have hu : f.1 = 0 := by
    change ((R).symm 0).1 = 0
    rw [map_zero]
    rfl
  rw [hp, hu, map_zero, sub_zero]

end Normalization

def planeColumn (e : PlaneEdge N) (k : Fin 2) : NormalizedInput K N :=
  (Pi.single e (Pi.single k 1), 0)

def rootColumn (r b a : Fin 3) : NormalizedInput K N :=
  (0, Pi.single r (Pi.single b (Pi.single a 1)))

/-- The plane and root standard columns expand every normalized input. -/
theorem normalizedInput_sum_columns (x : NormalizedInput K N) :
    x = (∑ c : PlaneEdge N × Fin 2, x.1 c.1 c.2 • planeColumn c.1 c.2) +
      ∑ c : Fin 3 × Fin 3 × Fin 3, x.2 c.1 c.2.1 c.2.2 • rootColumn c.1 c.2.1 c.2.2 := by
  classical
  apply Prod.ext
  · funext e k
    simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, planeColumn, rootColumn, smul_zero,
      Finset.sum_const_zero, add_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (e, k)]
    · simp
    · rintro ⟨e', k'⟩ _ hne
      by_cases he : e = e'
      · subst e'
        have hk : k ≠ k' := fun h => hne (Prod.ext rfl h.symm)
        simp [Pi.single_eq_of_ne hk]
      · simp [Pi.single_eq_of_ne he]
    · simp
  · funext r b a
    simp [planeColumn, rootColumn, Fintype.sum_prod_type, Prod.snd_sum, Finset.sum_apply,
      Pi.single_apply, mul_ite]

section ColumnSupport

variable [CharZero K]
variable (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K)
variable (hω : IsPrimitiveRoot ω 3) (hroots : ∀ r, rootParameters t r ≠ 0)
  (hinj : Function.Injective (rootParameters t))
  (hq : ∀ r b, chordFactor (rootParameters t r) (v b) ≠ 0)

@[simp] theorem normalizedCoefficient_planeColumn_self (e : PlaneEdge N) (k : Fin 2) :
    normalizedCoefficient ω t v hω hroots hinj hq (planeColumn e k) (planeEmbed e) =
      endpointVector t v (planeEmbed e) k := by
  fin_cases k <;> simp [planeColumn, normalizedCoefficient_plane_zeroRoot]

theorem normalizedCoefficient_planeColumn_off (e : PlaneEdge N) (k : Fin 2)
    {f : Edge N} (hne : f ≠ planeEmbed e) :
    normalizedCoefficient ω t v hω hroots hinj hq (planeColumn e k) f = 0 := by
  have hplane (e' : PlaneEdge N) (h : planeEmbed e' ≠ planeEmbed e) :
      normalizedCoefficient ω t v hω hroots hinj hq (planeColumn e k) (planeEmbed e') = 0 := by
    have he : e' ≠ e := fun he => h (congrArg planeEmbed he)
    simp [planeColumn, normalizedCoefficient_plane_zeroRoot, Pi.single_eq_of_ne he]
  rcases f with f | (f | ⟨r, b⟩)
  · exact hplane (.inl f) hne
  · exact hplane (.inr f) hne
  · exact normalizedCoefficient_root ω t v hω hroots hinj hq (planeColumn e k) r b

theorem normalizedCoefficient_rootColumn_apply (r b a r' b' : Fin 3) :
    normalizedCoefficient ω t v hω hroots hinj hq (rootColumn r b a) (rootEdge r' b') =
      (Pi.single r (Pi.single b (Pi.single a 1)) : RootBlockOutput K) r' b' :=
  normalizedCoefficient_root ω t v hω hroots hinj hq (rootColumn r b a) r' b'

@[simp] theorem normalizedCoefficient_rootColumn_self (r b a : Fin 3) :
    normalizedCoefficient ω t v hω hroots hinj hq (rootColumn r b a) (rootEdge r b) =
      Pi.single a 1 := by
  rw [normalizedCoefficient_rootColumn_apply, Pi.single_eq_same, Pi.single_eq_same]

theorem normalizedCoefficient_rootColumn_off (r b a r' b' : Fin 3) (hne : (r', b') ≠ (r, b)) :
    normalizedCoefficient ω t v hω hroots hinj hq (rootColumn r b a) (rootEdge r' b') = 0 := by
  rw [normalizedCoefficient_rootColumn_apply]
  by_cases hr : r' = r
  · subst r'
    have hb : b' ≠ b := fun h => hne (Prod.ext rfl h)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hb]
  · rw [Pi.single_eq_of_ne hr]
    rfl

end ColumnSupport

end IdealGeneration.TripleNormal.NormalizedEdgeColumns
