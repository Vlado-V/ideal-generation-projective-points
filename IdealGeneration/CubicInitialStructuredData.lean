module

public import IdealGeneration.CubicInitialPoints
public import IdealGeneration.CubicSupportedPattern

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The coordinate-simplex labels of the concrete initial C.2 cone. -/

namespace IdealGeneration.CubicInitial
open CubicSupported

private def edgePositions : Array ℕ := #[
  0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 9, 10, 11, 12, 13, 14, 15, 16, 0, 0, 0, 17, 18, 19, 20, 21,
  22, 23, 0, 0, 0, 0, 24, 25, 26, 27, 28, 29, 0, 0, 0, 0, 0, 30, 31, 32, 33, 34, 0, 0, 0, 0, 0,
  0, 35, 36, 37, 38, 0, 0, 0, 0, 0, 0, 0, 39, 40, 41, 0, 0, 0, 0, 0, 0, 0, 0, 42, 43, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
]

private def edgeStarts : Array ℕ := #[
  20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 49, 51, 53, 55, 57, 59, 61, 63, 64,
  66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106
]

private def edgeSlots : Array ℕ := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51,
  52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75,
  76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89
]

def edgeOrder : Fin 45 → Edge 10 := ![
  ⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(0, 3), by decide⟩, ⟨(0, 4), by decide⟩,
  ⟨(0, 5), by decide⟩, ⟨(0, 6), by decide⟩, ⟨(0, 7), by decide⟩, ⟨(0, 8), by decide⟩,
  ⟨(0, 9), by decide⟩, ⟨(1, 2), by decide⟩, ⟨(1, 3), by decide⟩, ⟨(1, 4), by decide⟩,
  ⟨(1, 5), by decide⟩, ⟨(1, 6), by decide⟩, ⟨(1, 7), by decide⟩, ⟨(1, 8), by decide⟩,
  ⟨(1, 9), by decide⟩, ⟨(2, 3), by decide⟩, ⟨(2, 4), by decide⟩, ⟨(2, 5), by decide⟩,
  ⟨(2, 6), by decide⟩, ⟨(2, 7), by decide⟩, ⟨(2, 8), by decide⟩, ⟨(2, 9), by decide⟩,
  ⟨(3, 4), by decide⟩, ⟨(3, 5), by decide⟩, ⟨(3, 6), by decide⟩, ⟨(3, 7), by decide⟩,
  ⟨(3, 8), by decide⟩, ⟨(3, 9), by decide⟩, ⟨(4, 5), by decide⟩, ⟨(4, 6), by decide⟩,
  ⟨(4, 7), by decide⟩, ⟨(4, 8), by decide⟩, ⟨(4, 9), by decide⟩, ⟨(5, 6), by decide⟩,
  ⟨(5, 7), by decide⟩, ⟨(5, 8), by decide⟩, ⟨(5, 9), by decide⟩, ⟨(6, 7), by decide⟩,
  ⟨(6, 8), by decide⟩, ⟨(6, 9), by decide⟩, ⟨(7, 8), by decide⟩, ⟨(7, 9), by decide⟩,
  ⟨(8, 9), by decide⟩
]


def edgePosition (e : Edge 10) : Fin 45 :=
  Fin.ofNat 45 edgePositions[10 * e.val.1.val + e.val.2.val]!

def vertexTraceIndex (i : Fin 10) : Fin 165 := i.castAdd 155

def edgeTraceIndex (e : Edge 10) : Fin 165 := (edgePosition e).natAdd 10 |>.castAdd 110

def freeTraceIndex (i : Fin 110) : Fin 165 := i.natAdd 55

def vertexConeIndex (i : Fin 10) (j : Fin 2) : Fin 108 :=
  Fin.ofNat 108 (2 * i.val + j.val)

def edgeConeIndex (e : Edge 10) (j : Fin 2) : Fin 108 :=
  Fin.ofNat 108 (edgeStarts[(edgePosition e).val]! + j.val)

def edgeSlotOf (i : Fin 88) : Edge 10 × Fin 2 :=
  let d := edgeSlots[i.val]!
  (edgeOrder (Fin.ofNat 45 (d / 2)), Fin.ofNat 2 (d % 2))

def vertexSlotOf (i : Fin 20) : Fin 10 × Fin 2 :=
  (Fin.ofNat 10 (i.val / 2), Fin.ofNat 2 (i.val % 2))

def slope (i : Fin 108) : ℕ := slopesData[i.val]!

def edgeScale (e : Edge 10) : ℕ := traceCoordinate (edgeTraceIndex e) e.val.2

end IdealGeneration.CubicInitial
