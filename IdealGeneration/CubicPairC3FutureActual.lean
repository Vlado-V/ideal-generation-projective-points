module

public import IdealGeneration.CubicPairC3Future
public import IdealGeneration.CubicPairC3Extension

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The local future condition controls the actual pair core in every ambient cone. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open CubicPair CubicMixedLocality RationalChart CubicParameterCompatibility

variable {K : Type*} [Field K] {k : ℕ}

/-- Restrict the enlarged cone to the local seven-coordinate chart. -/
def c3LocalChart (Q : Parameters K ((10 + 2 * k) + 2)) (hQ : Q.single = single) (j : Fin k) :
    Parameters K 7 where
  single := c3Parameters.single
  vertexSlope i := Q.vertexSlope (pairC3Ambient j i)
  vertexHeight i := Q.vertexHeight (pairC3Ambient j i)
  edgeSlope e := Q.edgeSlope (pairC3Edge j e)
  edgeHeight e := Q.edgeHeight (pairC3Edge j e)
  edgeLambda e := Q.edgeLambda (pairC3Edge j e)
  vertexSlope_ne i := Q.vertexSlope_ne (pairC3Ambient j i)
  vertexHeight_ne i := Q.vertexHeight_ne (pairC3Ambient j i)
  edgeSlope_ne e he := Q.edgeSlope_ne (pairC3Edge j e) (by rw [hQ, pairC3Edge_single]; exact he)
  edgeHeight_ne e := Q.edgeHeight_ne (pairC3Edge j e)
  edgeLambda_ne e := Q.edgeLambda_ne (pairC3Edge j e)

private theorem c3LocalChart_agreesAt (Q : Parameters K ((10 + 2 * k) + 2)) (hQ : Q.single = single)
    (j : Fin k) (a : Fin 4) : AgreesAt (c3LocalChart Q hQ j) Q (pairC3AmbientEmbedding j)
      (pairC3Ambient_strictMono j) (centerIndex a) := by
  refine ⟨rfl, rfl, fun e _ => ⟨?_, rfl, rfl, rfl⟩⟩
  change c3Parameters.single e = Q.single (pairC3Edge j e)
  rw [hQ, pairC3Edge_single]

private theorem primitiveValue_c3LocalChart (Q : Parameters K ((10 + 2 * k) + 2)) (hQ : Q.single = single)
    (j : Fin k) (i : PrimitiveIndex 7) : primitiveValue (c3LocalChart Q hQ j) i =
      primitiveValue Q (c3AmbientIndex j i) := by
  cases i <;> rfl

/-- Extract the genuinely new cone values and the samples of a pair. -/
def c3NewValue (Q : Parameters K ((10 + 2 * k) + 2)) (j : Fin k)
    (samples : Fin 13 → Fin 7 → K) : C3NewIndex → K
  | .inl i => primitiveValue Q (c3AmbientIndex j i.val)
  | .inr (r, i) => samples r i

/-- The actual current core determinant is detected by the local fiber. -/
theorem eval_c3FutureFiber_ne_zero_iff (P : Parameters K (10 + 2 * k))
    (Q : Parameters K ((10 + 2 * k) + 2)) (h : Compatible P Q) (hQ : Q.single = single)
    (j : Fin k) (D : PairBlockData K k j) (hD : D.coreColumn = canonicalPairCoreColumn j) :
    MvPolynomial.eval (c3NewValue Q j (fun i => pairC3Point j (D.point i) (D.weight i)))
      (c3FutureFiber (c3OldValue P j)) ≠ 0 ↔ (pairCoreMatrix (actualB7Data Q) D).det ≠ 0 := by
  let L := c3LocalChart Q hQ j
  let samples := fun i => pairC3Point j (D.point i) (D.weight i)
  have hOld : c3LocalOldValue L = c3OldValue P j := by
    funext i
    change primitiveValue L i.val = primitiveValue P (c3OldAmbientIndex j i)
    rw [primitiveValue_c3LocalChart, c3AmbientIndex_old, primitiveValue_oldPrimitiveIndex h]
  have hNew : c3LocalNewValue L samples = c3NewValue Q j samples := by
    funext i
    rcases i with i | ⟨r, d⟩
    · exact primitiveValue_c3LocalChart Q hQ j i.val
    · rfl
  have hm : pairCoreMatrix (actualB7Data Q) D = localC3Matrix L samples :=
    pairCoreMatrix_eq_localC3Matrix Q L j D hD (c3LocalChart_agreesAt Q hQ j)
  change MvPolynomial.eval (c3NewValue Q j samples) (c3FutureFiber (c3OldValue P j)) ≠ 0 ↔ _
  rw [hm, c3FutureFiber, eval_specialize_intSumPolynomial, ← hOld, ← hNew]
  exact eval_c3FutureCertificate_ne_zero_iff_local L rfl samples

/-- The rational C.3 patch supplies a retained condition on its compatible old chart. -/
theorem pairGood_of_compatible_c3Patch (P : Parameters ℚ (10 + 2 * k))
    (Q : Parameters ℚ ((10 + 2 * k) + 2)) (hQ : ∀ e, Q.single e = single e)
    (j : Fin k) (h : Compatible P (withC3Parameters Q hQ j)) : PairGood P j := by
  let D := c3PairBlockData ℚ j (fun _ => 1) (fun _ => one_ne_zero)
  have hdet : (pairCoreMatrix (actualB7Data (withC3Parameters Q hQ j)) D).det ≠ 0 :=
    actual_pairCoreMatrix_det_ne_zero_withC3Parameters Q hQ j _ _
  have he := (eval_c3FutureFiber_ne_zero_iff P _ h (funext hQ) j D rfl).mpr hdet
  intro hz
  exact he (by rw [hz, map_zero])

end IdealGeneration.CubicSupported.B5
