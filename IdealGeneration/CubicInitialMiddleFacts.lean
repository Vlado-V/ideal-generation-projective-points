module

public import IdealGeneration.CubicInitialMiddleData
public import IdealGeneration.CubicInitialMatrixData
public import IdealGeneration.ConeLookupGuards

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


namespace IdealGeneration.CubicInitial
open ConeMonomialChart

noncomputable instance normalInitialLookupDecidable (i : Fin 650) (j : Fin 12) :
    Decidable (NormalLookupValid (c := 2) (m := 10)
      normalExponent (quarticExponent i) j (normalLookup i j)) :=
  normalLookupValidDecidable (c := 2) (m := 10) _ _ _ _

/-- The predecessor and coefficient checks for a single C.2 middle row. -/
structure MiddleRowCertificate (i : Fin 650) : Prop where
  normalLookupValid : ∀ j : Fin 12, NormalLookupValid (c := 2) (m := 10)
    normalExponent (quarticExponent i) j (normalLookup i j)
  traceLookupValid : ∀ j, TraceLookupValid (c := 2) (m := 10)
    traceExponent (quarticExponent i) j (traceLookup i j)
  rowMatches : rawMiddleRow i = CertifiedRank.C2.originalRows i

end IdealGeneration.CubicInitial
