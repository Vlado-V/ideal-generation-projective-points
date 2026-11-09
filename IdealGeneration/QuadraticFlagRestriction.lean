module

public import IdealGeneration.QuadraticTraceRestriction
public import IdealGeneration.QuadraticFlagAssembly

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Restricting the paired flag along embeddings of base pairs and layers. -/

noncomputable section
namespace IdealGeneration.QuadraticFlagRestriction
open MvPolynomial QuadraticFlag QuadraticTraceRestriction

variable {P' P J' J : Type*}

/-- An embedding of base labels retains both coordinates of each pair. -/
def basePairEmbedding (f : P' ↪ P) : P' × Bool ↪ P × Bool :=
  f.prodMap (Function.Embedding.refl Bool)

@[simp] theorem basePairEmbedding_apply (f : P' ↪ P) (i : P' × Bool) :
    basePairEmbedding f i = (f i.1, i.2) := rfl

/-- The corresponding inclusion of the trace variables. -/
def flagTraceEmbedding (f : P' ↪ P) (g : J' ↪ J) : ((P' × Bool) ⊕ J') ↪ ((P × Bool) ⊕ J) :=
  (basePairEmbedding f).sumMap g

@[simp] theorem flagTraceEmbedding_inl (f : P' ↪ P) (g : J' ↪ J) (i : P' × Bool) :
    flagTraceEmbedding f g (.inl i) = Sum.inl (basePairEmbedding f i) := rfl

@[simp] theorem flagTraceEmbedding_inr (f : P' ↪ P) (g : J' ↪ J) (j : J') :
    flagTraceEmbedding f g (.inr j) = Sum.inr (g j) := rfl

/-- Include a flag label in the full family of flag points. -/
def mapFlagIndex (f : P' ↪ P) (g : J' ↪ J) : FlagIndex P' J' → FlagIndex P J
  | .base i => .base (basePairEmbedding f i)
  | .basePair i k => .basePair (basePairEmbedding f i) (basePairEmbedding f k)
  | .layer j => .layer (g j)
  | .layerPair p j => .layerPair (f p) (g j)

variable (K : Type*) [Field K] (f : P' ↪ P) (g : J' ↪ J)

/-- A smaller flag point extends by zero to its corresponding full flag point. -/
theorem extendPoint_flagPoint (t : FlagIndex P' J') :
    extendPoint K (flagTraceEmbedding f g) (flagPoint t) = flagPoint (mapFlagIndex f g t) := by
  classical
  cases t <;> simp only [flagPoint, mapFlagIndex, extendPoint_add, extendPoint_coordinate,
    flagTraceEmbedding_inl, flagTraceEmbedding_inr, basePairEmbedding_apply]

/-- Restriction sends every full flag equation to an equation of the smaller flag. -/
theorem restrictPolynomial_mem_flagVanishing {q : MvPolynomial ((P × Bool) ⊕ J) K}
    (hq : q ∈ flagVanishing (K := K) (P := P) (J := J)) :
    restrictPolynomial K (flagTraceEmbedding f g) q ∈ flagVanishing (K := K) (P := P') (J := J') := by
  change ∀ t : FlagIndex P J, eval (flagPoint t) q = 0 at hq
  change ∀ t : FlagIndex P' J', eval (flagPoint t) (restrictPolynomial K (flagTraceEmbedding f g) q) = 0
  intro t
  rw [eval_restrict, extendPoint_flagPoint]
  exact hq (mapFlagIndex f g t)

/-- Homogeneous quadratic restriction preserves the scalar flag ideal. -/
theorem restrictForm_mem_flagIdeal {q : Quadrics K ((P × Bool) ⊕ J)}
    (hq : q ∈ quadraticFlagVanishing (K := K) (P := P) (J := J)) :
    restrictForm K (flagTraceEmbedding f g) 2 q ∈
      quadraticFlagVanishing (K := K) (P := P') (J := J') := by
  exact restrictPolynomial_mem_flagVanishing K f g hq

/-- Both components of a restricted flag pair remain flag equations. -/
theorem restrictPair_mem_flagPairs
    {q : Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)}
    (hq : q ∈ (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
      (quadraticFlagVanishing (K := K) (P := P) (J := J))) :
    restrictPair K (flagTraceEmbedding f g) q ∈
      (quadraticFlagVanishing (K := K) (P := P') (J := J')).prod
      (quadraticFlagVanishing (K := K) (P := P') (J := J')) := by
  exact ⟨restrictForm_mem_flagIdeal K f g hq.1, restrictForm_mem_flagIdeal K f g hq.2⟩

end IdealGeneration.QuadraticFlagRestriction
