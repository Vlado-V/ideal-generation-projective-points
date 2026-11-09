module

public import IdealGeneration.TripleNormalScalarExtension
public import IdealGeneration.ConeSplitting

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The marked cone under enlargement

Old representatives and their marked supports are preserved. The two new
cone points over each new coordinate trace point have unit trace height.
-/

noncomputable section
namespace IdealGeneration.TripleNormal

variable {K : Type*} [Field K] {h p q r : ℕ}

/-- Extend a representative by adding three zero base coordinates. -/
def embedOldAmbient (x : Fin (3 + (h + 4)) → K) : Fin (3 + (h + 3 + 4)) → K :=
  Fin.append (fun j : Fin 3 => x (j.castAdd (h + 4)))
    (embedOldTrace (fun j : Fin (h + 4) => x (j.natAdd 3)))

/-- Coordinate inclusion of the original ambient space. -/
def oldAmbientIndex (h : ℕ) : Fin (3 + (h + 4)) → Fin (3 + (h + 3 + 4)) :=
  Fin.addCases (fun j : Fin 3 => j.castAdd (h + 3 + 4))
    (fun j : Fin (h + 4) => (oldTraceIndex h j).natAdd 3)

@[simp] theorem embedOldAmbient_oldAmbientIndex (x : Fin (3 + (h + 4)) → K) :
    embedOldAmbient x ∘ oldAmbientIndex h = x := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [embedOldAmbient, oldAmbientIndex]
  · have hi := congrFun (embedOldTrace_oldTraceIndex (fun k : Fin (h + 4) => x (k.natAdd 3))) i
    simpa only [embedOldAmbient, oldAmbientIndex, Function.comp_apply, Fin.addCases_right,
      Fin.append_right] using hi

private theorem embedOldTrace_mul (x : Fin (h + 4) → K) (a : K) :
    embedOldTrace (fun j => a * x j) = fun j => a * embedOldTrace x j := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [embedOldTrace]
  · simp [embedOldTrace]

/-- Append the six cone representatives above the three new coordinate
points, while appending all four groups of trace representatives. -/
def supportedExtension (C : ConeConfiguration K 3 (h + 4) p q)
    (a : Fin r × Fin (h + 3) → K) (ζ : Fin 4 → K) (normal : Fin 3 → Fin 2 → Fin 3 → K) :
    ConeConfiguration K 3 (h + 3 + 4) (p + 6) (q + (3 + (r + 4))) where
  trace := extensionTracePoints C.trace a ζ
  normal := Fin.append C.normal (fun j =>
    normal (finProdFinEquiv.symm j : Fin 3 × Fin 2).1 (finProdFinEquiv.symm j : Fin 3 × Fin 2).2)
  support := Fin.append (fun i => (C.support i).castAdd (3 + (r + 4))) (fun j =>
    (((finProdFinEquiv.symm j : Fin 3 × Fin 2).1).castAdd (r + 4)).natAdd q)
  height := Fin.append C.height (fun _ => 1)

variable (C : ConeConfiguration K 3 (h + 4) p q)
  (a : Fin r × Fin (h + 3) → K) (ζ : Fin 4 → K) (normal : Fin 3 → Fin 2 → Fin 3 → K)

@[simp] theorem supportedExtension_trace_old (i : Fin q) :
    (supportedExtension C a ζ normal).trace (i.castAdd (3 + (r + 4))) =
      embedOldTrace (C.trace i) := by
  simp [supportedExtension, extensionTracePoints]

@[simp] theorem supportedExtension_trace_coordinate (b : Fin 3) :
    (supportedExtension C a ζ normal).trace ((b.castAdd (r + 4)).natAdd q) =
      extensionCoordinate h b := by
  simp [supportedExtension, extensionTracePoints]

@[simp] theorem supportedExtension_trace_free (i : Fin r) :
    (supportedExtension C a ζ normal).trace (((i.castAdd 4).natAdd 3).natAdd q) =
      extensionFreePoint (fun j => a (i, j)) := by
  simp [supportedExtension, extensionTracePoints]

@[simp] theorem supportedExtension_trace_layer (j : Fin 4) :
    (supportedExtension C a ζ normal).trace (((j.natAdd r).natAdd 3).natAdd q) =
      extensionLayer h ζ j := by
  simp [supportedExtension, extensionTracePoints]

@[simp] theorem supportedExtension_normal_old (i : Fin p) :
    (supportedExtension C a ζ normal).normal (i.castAdd 6) = C.normal i := by
  simp [supportedExtension]

@[simp] theorem supportedExtension_height_old (i : Fin p) :
    (supportedExtension C a ζ normal).height (i.castAdd 6) = C.height i := by
  simp [supportedExtension]

@[simp] theorem supportedExtension_support_old (i : Fin p) :
    (supportedExtension C a ζ normal).support (i.castAdd 6) =
      (C.support i).castAdd (3 + (r + 4)) := by
  simp [supportedExtension]

@[simp] theorem supportedExtension_normal_new (b : Fin 3) (k : Fin 2) :
    (supportedExtension C a ζ normal).normal ((finProdFinEquiv (b, k)).natAdd p) =
      normal b k := by
  simp [supportedExtension]

@[simp] theorem supportedExtension_height_new (b : Fin 3) (k : Fin 2) :
    (supportedExtension C a ζ normal).height ((finProdFinEquiv (b, k)).natAdd p) = 1 := by
  simp [supportedExtension]

@[simp] theorem supportedExtension_support_new (b : Fin 3) (k : Fin 2) :
    (supportedExtension C a ζ normal).support ((finProdFinEquiv (b, k)).natAdd p) =
      (b.castAdd (r + 4)).natAdd q := by
  simp [supportedExtension]

/-- Old cone points are precisely the zero-extended representatives. -/
theorem supportedExtension_point_old (i : Fin p) :
    (supportedExtension C a ζ normal).point (i.castAdd 6) = embedOldAmbient (C.point i) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp [ConeConfiguration.point, embedOldAmbient]
  · have hk := congrFun (embedOldTrace_mul (C.trace (C.support i)) (C.height i)) k
    simpa only [ConeConfiguration.point, embedOldAmbient, Fin.addCases_right, Fin.append_right,
      supportedExtension_height_old, supportedExtension_support_old, supportedExtension_trace_old]
      using hk.symm

/-- Each new pair has the specified normals and one coordinate trace support. -/
theorem supportedExtension_point_new (b : Fin 3) (k : Fin 2) :
    (supportedExtension C a ζ normal).point ((finProdFinEquiv (b, k)).natAdd p) =
      Fin.append (normal b k) (extensionCoordinate h b) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [ConeConfiguration.point, Fin.addCases_left, Fin.append_left]
    rw [supportedExtension_normal_new C a ζ normal b k]
  · simp only [ConeConfiguration.point, Fin.addCases_right, Fin.append_right]
    rw [supportedExtension_height_new C a ζ normal b k, supportedExtension_support_new C a ζ normal b k,
      supportedExtension_trace_coordinate C a ζ normal b, one_mul]

/-- The inclusion of old coordinates recovers every old cone point. -/
theorem supportedExtension_point_restrict (i : Fin p) :
    (supportedExtension C a ζ normal).point (i.castAdd 6) ∘ oldAmbientIndex h = C.point i := by
  rw [supportedExtension_point_old, embedOldAmbient_oldAmbientIndex]

/-- The inclusion of old coordinates recovers every old trace representative. -/
theorem supportedExtension_trace_restrict (i : Fin q) :
    (supportedExtension C a ζ normal).trace (i.castAdd (3 + (r + 4))) ∘ oldTraceIndex h =
      C.trace i := by
  rw [supportedExtension_trace_old, embedOldTrace_oldTraceIndex]

end IdealGeneration.TripleNormal
