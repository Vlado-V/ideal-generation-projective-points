module

public import IdealGeneration.CubicB11Actual
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The primitive cone data and pool probes of the C.2 sample. -/

namespace IdealGeneration.CubicSupported.B7Root

open B5

private def slopes : Array ℕ :=
  #[235, 654, 243, 858, 961, 8, 1, 133, 904, 519, 371, 748, 670, 925, 1002, 112,
  90, 284, 880, 157, 677, 781, 60, 442, 0, 0, 82, 503, 612, 189, 747, 737,
  519, 52, 368, 843, 198, 245, 997, 113, 113, 14, 588, 360, 817, 0, 970, 555,
  0, 0, 0, 0, 704, 288, 382, 915, 350, 721, 143, 135, 357, 1001, 922, 792,
  462, 223, 223, 465, 200, 0, 650, 318, 0, 0, 0, 0, 0, 0, 391, 385,
  390, 755, 671, 184, 139, 465, 466, 6, 507, 128, 492, 216, 888, 0, 324, 477,
  0, 0, 0, 0, 0, 0, 0, 0, 549, 511, 130, 173, 988, 362, 197, 721,
  404, 146, 250, 184, 264, 0, 346, 544, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 923, 267, 575, 968, 562, 74, 856, 332, 894, 35, 864, 687, 633, 117,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 751, 546, 454, 495,
  953, 923, 284, 578, 115, 399, 555, 143, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 66, 27, 259, 347, 376, 941, 945, 421, 41, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  720, 311, 326, 579, 675, 705, 260, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 346, 605, 906, 723, 418, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 771, 585, 166, 332, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 357, 40]

private def heights : Array ℕ :=
  #[818, 355, 737, 511, 223, 442, 68, 1001, 49, 229, 659, 166, 831, 577, 496, 924,
  353, 330, 719, 170, 212, 32, 816, 233, 1, 1, 999, 873, 551, 957, 948, 471,
  165, 695, 940, 24, 880, 70, 399, 189, 189, 822, 54, 790, 294, 1, 285, 128,
  1, 1, 1, 1, 373, 793, 414, 255, 144, 108, 13, 220, 704, 715, 101, 502,
  162, 282, 282, 97, 359, 1, 665, 793, 1, 1, 1, 1, 1, 1, 857, 894,
  451, 731, 567, 64, 216, 876, 540, 251, 899, 477, 538, 104, 771, 1, 918, 628,
  1, 1, 1, 1, 1, 1, 1, 1, 334, 158, 792, 62, 995, 58, 291, 795,
  943, 919, 286, 1003, 890, 1, 43, 813, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 18, 169, 265, 504, 481, 837, 634, 403, 596, 204, 125, 422, 848, 805,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 542, 949, 287, 20,
  513, 480, 622, 433, 102, 404, 123, 823, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 763, 741, 312, 163, 455, 953, 972, 388, 933, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  350, 211, 849, 517, 602, 660, 823, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 942, 40, 790, 750, 302, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 957, 475, 25, 336, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 830, 475]

private def lambdas : Array ℕ :=
  #[1, 779, 930, 620, 764, 650, 866, 418, 740, 302, 194, 902, 1, 1, 533, 862,
  326, 522, 246, 380, 304, 566, 768, 309, 1, 1, 1, 699, 144, 813, 91, 1001,
  198, 843, 368, 755, 1, 1, 1, 1, 705, 501, 645, 602, 828, 641, 837, 155,
  1, 1, 1, 1, 1, 954, 613, 807, 68, 558, 296, 406, 1, 1, 1, 1,
  1, 1, 295, 607, 64, 107, 185, 263, 1, 1, 1, 1, 1, 1, 1, 865,
  126, 919, 883, 613, 1, 1, 1, 1, 1, 1, 1, 1, 157, 659, 357, 406,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 963, 296, 245, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 790, 479, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 998, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def slopeNat (i j : Fin 12) (d : Fin 2) : ℕ := slopes[2 * (12 * i.val + j.val) + d.val]?.getD 0
def heightNat (i j : Fin 12) (d : Fin 2) : ℕ := heights[2 * (12 * i.val + j.val) + d.val]?.getD 1
def lambdaNat (i j : Fin 12) : ℕ := lambdas[12 * i.val + j.val]?.getD 1

set_option maxRecDepth 4096 in
private theorem slope_vertex_check : ∀ i : Fin 12,
    (slopeNat i i 0 : ZMod 1009) ≠ (slopeNat i i 1 : ZMod 1009) := by decide +kernel

set_option maxRecDepth 4096 in
private theorem slope_double_check : ∀ i j : Fin 12, i < j →
    decide (B5.singleLabels i.val j.val) = false →
      (slopeNat i j 0 : ZMod 1009) ≠ (slopeNat i j 1 : ZMod 1009) := by decide +kernel

set_option maxRecDepth 4096 in
private theorem height_check : ∀ (i j : Fin 12) (d : Fin 2),
    (heightNat i j d : ZMod 1009) ≠ 0 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem lambda_check : ∀ i j : Fin 12, (lambdaNat i j : ZMod 1009) ≠ 0 := by decide +kernel

/-- The extended cone chart realized by natural-number coefficients. -/
def parameters (K : Type*) [Field K]
    (hne : ∀ a b : ℕ, (a : ZMod 1009) ≠ (b : ZMod 1009) → (a : K) ≠ (b : K)) :
    Parameters K 12 where
  single := B5.single
  vertexSlope i d := slopeNat i i d
  vertexHeight i d := heightNat i i d
  edgeSlope e d := slopeNat e.val.1 e.val.2 d
  edgeHeight e d := heightNat e.val.1 e.val.2 d
  edgeLambda e := lambdaNat e.val.1 e.val.2
  vertexSlope_ne i := hne _ _ (slope_vertex_check i)
  vertexHeight_ne i d := by simpa only [Nat.cast_zero] using hne _ 0 (height_check i i d)
  edgeSlope_ne e he := hne _ _ (slope_double_check e.val.1 e.val.2 e.property he)
  edgeHeight_ne e d := by simpa only [Nat.cast_zero] using hne _ 0 (height_check e.val.1 e.val.2 d)
  edgeLambda_ne e := by simpa only [Nat.cast_zero] using hne _ 0 (lambda_check e.val.1 e.val.2)

def parametersCharZero (K : Type*) [Field K] [CharZero K] : Parameters K 12 :=
  parameters K fun _ _ h he => h (congrArg (fun n : ℕ => (n : ZMod 1009)) (Nat.cast_injective he))

private def sample0 : Array (Fin 10 × Option (Fin 10 × ℕ)) :=
  #[(1, none), (2, none), (3, none), (4, none), (0, some (1, 676)),
  (0, some (2, 633)), (0, some (3, 512)), (0, some (4, 159)), (1, some (2, 427)), (1, some (3, 640)),
  (1, some (4, 29)), (1, some (5, 924)), (1, some (6, 656)), (1, some (7, 506)), (1, some (8, 130)),
  (1, some (9, 518)), (2, some (3, 144)), (2, some (4, 594)), (2, some (5, 676)), (2, some (6, 804)),
  (2, some (7, 696)), (2, some (8, 324)), (2, some (9, 520)), (3, some (4, 425)), (3, some (5, 993)),
  (3, some (6, 86)), (3, some (7, 678)), (3, some (8, 576)), (3, some (9, 199)), (4, some (5, 842)),
  (4, some (6, 560)), (4, some (7, 755)), (4, some (8, 55)), (4, some (9, 905)), (5, none),
  (6, none), (7, none), (8, none), (9, none), (0, none),
  (7, some (8, 678)), (7, some (9, 741)), (8, some (9, 324))]

private def sample1 : Array (Fin 10 × Option (Fin 10 × ℕ)) :=
  #[(7, none), (8, none), (9, none), (0, some (7, 922)), (0, some (8, 604)),
  (0, some (9, 335)), (1, some (7, 344)), (1, some (8, 742)), (1, some (9, 477)), (2, some (7, 697)),
  (2, some (8, 247)), (2, some (9, 730)), (3, some (7, 994)), (3, some (8, 104)), (3, some (9, 598)),
  (4, some (7, 671)), (4, some (8, 560)), (4, some (9, 607)), (5, some (7, 889)), (5, some (8, 858)),
  (5, some (9, 121)), (6, some (7, 873)), (6, some (8, 510)), (6, some (9, 436)), (7, some (8, 950)),
  (7, some (9, 852)), (8, some (9, 887)), (0, none), (1, none), (2, none),
  (3, none), (4, none), (5, none), (6, none), (1, some (2, 710)),
  (1, some (3, 654)), (2, some (3, 576))]

/-- The first coordinate is one. The optional second coordinate carries its sample value. -/
def sampleSupport (p : Fin 10 × Option (Fin 10 × ℕ)) : Finset (Fin 10) :=
  match p.2 with
  | none => {p.1}
  | some (j, _) => {p.1, j}

def sampleCoordinate (p : Fin 10 × Option (Fin 10 × ℕ)) (i : Fin 10) : ℕ :=
  if i = p.1 then 1 else
    match p.2 with
    | none => 0
    | some (j, a) => if i = j then a else 0

theorem sampleCoordinate_eq_zero (p : Fin 10 × Option (Fin 10 × ℕ)) (i : Fin 10)
    (hi : i ∉ sampleSupport p) : sampleCoordinate p i = 0 := by
  rcases p with ⟨j, _ | ⟨k, a⟩⟩ <;> simp_all [sampleSupport, sampleCoordinate]

def point0 (i : Fin 43) := sample0[i.val]?.getD (0, none)
def point1 (i : Fin 37) := sample1[i.val]?.getD (0, none)

/-- Interleave the two normal components at each sample. -/
def rowIndex {n : ℕ} (i : Fin (n * 2)) : Fin n × Fin 2 := finProdFinEquiv.symm i

def probe0 (K : Type*) [Field K] (i : Fin 86) : B11Probe K 10 :=
  ⟨fun j => sampleCoordinate (point0 (rowIndex (n := 43) i).1) j, pureDirection 0, (rowIndex (n := 43) i).2⟩

def probe1 (K : Type*) [Field K] (i : Fin 74) : B11Probe K 10 :=
  ⟨fun j => sampleCoordinate (point1 (rowIndex (n := 37) i).1) j, pureDirection 1, (rowIndex (n := 37) i).2⟩

private def oldSingle0 : {e : Edge 10 // B5.single e = true} :=
  ⟨⟨(1, 7), by decide⟩, by decide⟩

private def oldSingle1 : {e : Edge 10 // B5.single e = true} :=
  ⟨⟨(2, 8), by decide⟩, by decide⟩

private def neighbor0_1 : {i : Fin 10 // neighbor 0 i} := ⟨1, by decide⟩

private def neighbor0_2 : {i : Fin 10 // neighbor 0 i} := ⟨2, by decide⟩

private def neighbor0_3 : {i : Fin 10 // neighbor 0 i} := ⟨3, by decide⟩

private def neighbor0_4 : {i : Fin 10 // neighbor 0 i} := ⟨4, by decide⟩

private def columns0 : Array (B7Column 10) :=
  #[.localColumn 0 (.inl oldSingle0), .localColumn 0 (.inl oldSingle1), .localColumn 0 (.inr (neighbor0_1, 0)),
  .localColumn 0 (.inr (neighbor0_1, 1)), .localColumn 0 (.inr (neighbor0_1, 2)), .localColumn 0 (.inr (neighbor0_1, 3)),
  .localColumn 0 (.inr (neighbor0_1, 4)), .localColumn 0 (.inr (neighbor0_1, 5)), .localColumn 0 (.inr (neighbor0_1, 6)),
  .localColumn 0 (.inr (neighbor0_1, 7)), .localColumn 0 (.inr (neighbor0_1, 8)), .localColumn 0 (.inr (neighbor0_1, 9)),
  .localColumn 0 (.inr (neighbor0_2, 0)), .localColumn 0 (.inr (neighbor0_2, 1)), .localColumn 0 (.inr (neighbor0_2, 2)),
  .localColumn 0 (.inr (neighbor0_2, 3)), .localColumn 0 (.inr (neighbor0_2, 4)), .localColumn 0 (.inr (neighbor0_2, 5)),
  .localColumn 0 (.inr (neighbor0_2, 6)), .localColumn 0 (.inr (neighbor0_2, 7)), .localColumn 0 (.inr (neighbor0_2, 8)),
  .localColumn 0 (.inr (neighbor0_2, 9)), .localColumn 0 (.inr (neighbor0_3, 0)), .localColumn 0 (.inr (neighbor0_3, 1)),
  .localColumn 0 (.inr (neighbor0_3, 2)), .localColumn 0 (.inr (neighbor0_3, 3)), .localColumn 0 (.inr (neighbor0_3, 4)),
  .localColumn 0 (.inr (neighbor0_3, 5)), .localColumn 0 (.inr (neighbor0_3, 6)), .localColumn 0 (.inr (neighbor0_3, 7)),
  .localColumn 0 (.inr (neighbor0_3, 8)), .localColumn 0 (.inr (neighbor0_3, 9)), .localColumn 0 (.inr (neighbor0_4, 0)),
  .localColumn 0 (.inr (neighbor0_4, 1)), .localColumn 0 (.inr (neighbor0_4, 2)), .localColumn 0 (.inr (neighbor0_4, 3)),
  .localColumn 0 (.inr (neighbor0_4, 4)), .localColumn 0 (.inr (neighbor0_4, 5)), .localColumn 0 (.inr (neighbor0_4, 6)),
  .localColumn 0 (.inr (neighbor0_4, 7)), .localColumn 0 (.inr (neighbor0_4, 8)), .localColumn 0 (.inr (neighbor0_4, 9)),
  .motion 0 0 0, .motion 0 0 1, .motion 0 0 2,
  .motion 0 1 0, .motion 0 1 1, .motion 0 1 2,
  .motion 0 2 0, .motion 0 2 1, .motion 0 2 2,
  .motion 0 3 0, .motion 0 3 1, .motion 0 3 2,
  .motion 0 4 0, .motion 0 4 1, .motion 0 4 2,
  .motion 0 5 0, .motion 0 5 1, .motion 0 5 2,
  .motion 0 6 0, .motion 0 6 1, .motion 0 6 2,
  .motion 0 7 0, .motion 0 7 1, .motion 0 7 2,
  .motion 0 8 0, .motion 0 8 1, .motion 0 8 2,
  .motion 0 9 0, .motion 0 9 1, .motion 0 9 2,
  .extra 0 neighbor0_1 0, .extra 0 neighbor0_1 1, .extra 0 neighbor0_2 0,
  .extra 0 neighbor0_2 1, .extra 0 neighbor0_3 0, .extra 0 neighbor0_3 1,
  .extra 0 neighbor0_4 0, .extra 0 neighbor0_4 1, .remaining 0 0 0,
  .remaining 0 0 1, .remaining 0 0 2, .remaining 0 1 0,
  .remaining 0 1 1, .remaining 0 1 2]

def column0 (j : Fin 86) : B7Column 10 :=
  columns0[j.val]?.getD (.motion 0 0 0)

theorem column0_direction : ∀ j, b7Direction (column0 j) = 0 := by decide +kernel

theorem column0_pool : ∀ j, b7Owner (column0 j) = none := by decide +kernel

private def neighbor1_7 : {i : Fin 10 // neighbor 1 i} := ⟨7, by decide⟩

private def neighbor1_8 : {i : Fin 10 // neighbor 1 i} := ⟨8, by decide⟩

private def neighbor1_9 : {i : Fin 10 // neighbor 1 i} := ⟨9, by decide⟩

private def columns1 : Array (B7Column 10) :=
  #[.localColumn 1 (.inl oldSingle0), .localColumn 1 (.inl oldSingle1), .localColumn 1 (.inr (neighbor1_7, 0)),
  .localColumn 1 (.inr (neighbor1_7, 1)), .localColumn 1 (.inr (neighbor1_7, 2)), .localColumn 1 (.inr (neighbor1_7, 3)),
  .localColumn 1 (.inr (neighbor1_7, 4)), .localColumn 1 (.inr (neighbor1_7, 5)), .localColumn 1 (.inr (neighbor1_7, 6)),
  .localColumn 1 (.inr (neighbor1_7, 7)), .localColumn 1 (.inr (neighbor1_7, 8)), .localColumn 1 (.inr (neighbor1_7, 9)),
  .localColumn 1 (.inr (neighbor1_8, 0)), .localColumn 1 (.inr (neighbor1_8, 1)), .localColumn 1 (.inr (neighbor1_8, 2)),
  .localColumn 1 (.inr (neighbor1_8, 3)), .localColumn 1 (.inr (neighbor1_8, 4)), .localColumn 1 (.inr (neighbor1_8, 5)),
  .localColumn 1 (.inr (neighbor1_8, 6)), .localColumn 1 (.inr (neighbor1_8, 7)), .localColumn 1 (.inr (neighbor1_8, 8)),
  .localColumn 1 (.inr (neighbor1_8, 9)), .localColumn 1 (.inr (neighbor1_9, 0)), .localColumn 1 (.inr (neighbor1_9, 1)),
  .localColumn 1 (.inr (neighbor1_9, 2)), .localColumn 1 (.inr (neighbor1_9, 3)), .localColumn 1 (.inr (neighbor1_9, 4)),
  .localColumn 1 (.inr (neighbor1_9, 5)), .localColumn 1 (.inr (neighbor1_9, 6)), .localColumn 1 (.inr (neighbor1_9, 7)),
  .localColumn 1 (.inr (neighbor1_9, 8)), .localColumn 1 (.inr (neighbor1_9, 9)), .motion 1 0 0,
  .motion 1 0 1, .motion 1 0 2, .motion 1 1 0,
  .motion 1 1 1, .motion 1 1 2, .motion 1 2 0,
  .motion 1 2 1, .motion 1 2 2, .motion 1 3 0,
  .motion 1 3 1, .motion 1 3 2, .motion 1 4 0,
  .motion 1 4 1, .motion 1 4 2, .motion 1 5 0,
  .motion 1 5 1, .motion 1 5 2, .motion 1 6 0,
  .motion 1 6 1, .motion 1 6 2, .motion 1 7 0,
  .motion 1 7 1, .motion 1 7 2, .motion 1 8 0,
  .motion 1 8 1, .motion 1 8 2, .motion 1 9 0,
  .motion 1 9 1, .motion 1 9 2, .extra 1 neighbor1_7 0,
  .extra 1 neighbor1_7 1, .extra 1 neighbor1_8 0, .extra 1 neighbor1_8 1,
  .extra 1 neighbor1_9 0, .extra 1 neighbor1_9 1, .remaining 1 0 0,
  .remaining 1 0 1, .remaining 1 0 2, .remaining 1 1 0,
  .remaining 1 1 1, .remaining 1 1 2]

def column1 (j : Fin 74) : B7Column 10 :=
  columns1[j.val]?.getD (.motion 1 0 0)

theorem column1_direction : ∀ j, b7Direction (column1 j) = 1 := by decide +kernel

theorem column1_pool : ∀ j, b7Owner (column1 j) = none := by decide +kernel

abbrev Index := Fin 86 ⊕ Fin 74

def pool (K : Type*) [Field K] : PoolBlockData K 10 Index where
  probe := Sum.elim (probe0 K) (probe1 K)
  column := Sum.elim column0 column1
  supported _ i hi := False.elim (Nat.not_le_of_lt i.isLt hi)
  columnPool := Sum.rec column0_pool column1_pool

end IdealGeneration.CubicSupported.B7Root
