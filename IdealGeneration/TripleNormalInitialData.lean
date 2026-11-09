module

public import IdealGeneration.ConeSplitting
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Exact data for the three-normal initial configuration

The literal tables are Tables 1–3 of Appendix A.4. Monomial and pivot
indices use the stated lexicographic ordering, with zero-based Lean indices.
The first sixteen cone representatives retain the symbolic cube-root
parameter so the same definitions specialize in both characteristics.
-/

noncomputable section
namespace IdealGeneration.TripleNormalInitial
open MvPolynomial
set_option maxRecDepth 4096

/-- Table 1, free base trace points. -/
def table1 : Fin 24 → Fin 8 → ℕ :=
  ![![138, 583, 868, 822, 783, 65, 262, 121],
    ![508, 780, 461, 484, 668, 389, 808, 215],
    ![97, 500, 30, 915, 856, 400, 444, 623],
    ![781, 786, 3, 713, 457, 273, 739, 822],
    ![235, 606, 968, 105, 924, 326, 32, 23],
    ![27, 666, 555, 10, 962, 903, 391, 703],
    ![222, 993, 433, 744, 30, 541, 228, 783],
    ![449, 962, 508, 567, 239, 354, 237, 694],
    ![225, 780, 471, 976, 297, 949, 23, 427],
    ![858, 939, 570, 945, 658, 103, 191, 645],
    ![742, 881, 304, 124, 761, 341, 918, 739],
    ![997, 729, 513, 959, 991, 433, 520, 850],
    ![933, 687, 195, 311, 291, 602, 997, 904],
    ![512, 867, 964, 518, 403, 604, 874, 36],
    ![492, 249, 762, 817, 414, 425, 681, 178],
    ![376, 562, 904, 720, 795, 691, 756, 384],
    ![89, 450, 680, 521, 111, 798, 168, 534],
    ![861, 403, 380, 502, 751, 31, 481, 45],
    ![316, 721, 869, 1007, 630, 608, 593, 404],
    ![663, 175, 173, 515, 233, 1006, 13, 790],
    ![205, 553, 943, 881, 562, 238, 415, 527],
    ![353, 976, 868, 592, 362, 471, 932, 276],
    ![676, 562, 624, 981, 747, 6, 393, 803],
    ![878, 841, 978, 908, 961, 759, 525, 829]]

/-- The three layer heights of Table 2. -/
def table2Zeta : Fin 4 → Fin 3 → ℕ :=
  ![![133, 532, 797],
    ![568, 205, 964],
    ![554, 639, 806],
    ![564, 599, 186]]

/-- The three normal vectors in each record of Table 2. -/
def table2Normal : Fin 4 → Fin 3 → Fin 3 → ℕ :=
  ![![![575, 211, 437], ![973, 58, 493], ![891, 374, 584]],
    ![![517, 424, 497], ![833, 366, 425], ![355, 2, 552]],
    ![![628, 340, 470], ![615, 29, 824], ![236, 651, 182]],
    ![![882, 94, 818], ![565, 817, 872], ![837, 954, 262]]]

/-- Table 3, the final four trace points. -/
def table3 : Fin 4 → Fin 12 → ℕ :=
  ![![34, 862, 967, 690, 73, 86, 889, 18, 464, 15, 773, 774],
    ![288, 256, 276, 113, 817, 640, 190, 353, 298, 72, 172, 164],
    ![262, 541, 975, 173, 673, 280, 664, 729, 302, 466, 720, 330],
    ![509, 486, 117, 25, 320, 396, 352, 432, 816, 193, 265, 112]]

def baseTrace (i : Fin 8) (j : Fin 12) : ℤ :=
  if j.val = i.val then 1 else 0

def freeTrace (i : Fin 24) (j : Fin 12) : ℤ :=
  Fin.addCases (fun k : Fin 8 => (table1 i k : ℤ)) (fun _ : Fin 4 => 0) j

def layerTrace (j l : Fin 4) (k : Fin 12) : ℤ :=
  Fin.cases (if k.val = 8 + j.val then 1 else 0)
    (fun ν : Fin 3 => Fin.addCases
      (fun i : Fin 8 => if i.val / 3 = ν.val then 1 else 0)
      (fun k : Fin 4 => if k = j then (table2Zeta j ν : ℤ) else 0) k) l

/-- The 52 trace representatives, ordered as in the calculation. -/
def traceIntegers (i : Fin 52) (j : Fin 12) : ℤ :=
  Fin.addCases (fun k : Fin 8 => baseTrace k j) (fun k : Fin 44 =>
    Fin.addCases (fun l : Fin 24 => freeTrace l j) (fun l : Fin 20 =>
      Fin.addCases (fun r : Fin 16 =>
        let ji := (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm r
        layerTrace ji.1 ji.2 j) (fun r : Fin 4 => (table3 r j : ℤ)) l) k) i

/-- The cone-to-trace label assignment, including two cone points over
 each of the eight base coordinates. -/
def support (k : Fin 28) : Fin 52 :=
  Fin.addCases (fun i : Fin 16 => ⟨i.val / 2, by omega⟩)
    (fun i : Fin 12 => ⟨32 + 4 * (i.val / 3) + i.val % 3, by omega⟩) k

/-- Formula (A.9) before specialization. The two branches are `θ₊σ₊`
 and `θ₋σ₋` with `tᵢ = i + 1`. -/
def baseNormalPolynomial (i : Fin 8) (branch : Fin 2) (j : Fin 3) : Polynomial ℤ :=
  let t : Polynomial ℤ := ((i.val + 1 : ℕ) : Polynomial ℤ)
  let ω : Polynomial ℤ := Polynomial.X
  if branch = 0 then
    -(ω ^ 2) * (![ω ^ 2 * t ^ 2, ω * t, 1] : Fin 3 → Polynomial ℤ) j
  else
    ω * (![ω * t ^ 2, ω ^ 2 * t, 1] : Fin 3 → Polynomial ℤ) j

def normalPolynomial (i : Fin 28) (j : Fin 3) : Polynomial ℤ :=
  Fin.addCases (fun k : Fin 16 =>
    let ib := (finProdFinEquiv : Fin 8 × Fin 2 ≃ Fin 16).symm k
    baseNormalPolynomial ib.1 ib.2 j)
    (fun k : Fin 12 =>
      let ji := (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).symm k
      Polynomial.C (table2Normal ji.1 ji.2 j : ℤ)) i

def pointPolynomial (i : Fin 28) (j : Fin 15) : Polynomial ℤ :=
  Fin.addCases (normalPolynomial i) (fun k => Polynomial.C (traceIntegers (support i) k)) j

def tracePolynomial (i : Fin 52) (j : Fin 12) : Polynomial ℤ :=
  Polynomial.C (traceIntegers i j)

/-- Specialize the symbolic data to actual marked cone representatives. -/
def configuration {K : Type*} [Field K] (ω : K) : ConeConfiguration K 3 12 28 52 where
  trace i j := traceIntegers i j
  normal i j := (normalPolynomial i j).eval₂ (Int.castRingHom K) ω
  support := support
  height _ := 1

@[simp] theorem configuration_point_eq_eval {K : Type*} [Field K] (ω : K)
    (i : Fin 28) (j : Fin 15) :
    (configuration ω).point i j = (pointPolynomial i j).eval₂ (Int.castRingHom K) ω := by
  refine Fin.addCases (motive := fun j => (configuration ω).point i j =
    (pointPolynomial i j).eval₂ (Int.castRingHom K) ω) (fun k : Fin 3 => ?_)
    (fun k : Fin 12 => ?_) j
  · simp only [configuration, ConeConfiguration.point, pointPolynomial, Fin.addCases_left]
  · simp only [configuration, ConeConfiguration.point, pointPolynomial, Fin.addCases_right,
      one_mul, Polynomial.eval₂_C]
    rfl

@[simp] theorem configuration_trace_eq_eval {K : Type*} [Field K] (ω : K)
    (i : Fin 52) (j : Fin 12) :
    (configuration ω).trace i j = (tracePolynomial i j).eval₂ (Int.castRingHom K) ω := by
  simp only [configuration, tracePolynomial, Polynomial.eval₂_C]
  rfl

/-- The 42 normal-ideal quadratic monomials in lexicographic order. -/
def normalQuadraticTuple : Fin 42 → Fin 3 × Fin 15 :=
  ![(0, 0),
    (0, 1),
    (0, 2),
    (0, 3),
    (0, 4),
    (0, 5),
    (0, 6),
    (0, 7),
    (0, 8),
    (0, 9),
    (0, 10),
    (0, 11),
    (0, 12),
    (0, 13),
    (0, 14),
    (1, 1),
    (1, 2),
    (1, 3),
    (1, 4),
    (1, 5),
    (1, 6),
    (1, 7),
    (1, 8),
    (1, 9),
    (1, 10),
    (1, 11),
    (1, 12),
    (1, 13),
    (1, 14),
    (2, 2),
    (2, 3),
    (2, 4),
    (2, 5),
    (2, 6),
    (2, 7),
    (2, 8),
    (2, 9),
    (2, 10),
    (2, 11),
    (2, 12),
    (2, 13),
    (2, 14)]

/-- All 78 trace quadrics in lexicographic order. -/
def traceQuadraticTuple : Fin 78 → Fin 12 × Fin 12 :=
  ![(0, 0),
    (0, 1),
    (0, 2),
    (0, 3),
    (0, 4),
    (0, 5),
    (0, 6),
    (0, 7),
    (0, 8),
    (0, 9),
    (0, 10),
    (0, 11),
    (1, 1),
    (1, 2),
    (1, 3),
    (1, 4),
    (1, 5),
    (1, 6),
    (1, 7),
    (1, 8),
    (1, 9),
    (1, 10),
    (1, 11),
    (2, 2),
    (2, 3),
    (2, 4),
    (2, 5),
    (2, 6),
    (2, 7),
    (2, 8),
    (2, 9),
    (2, 10),
    (2, 11),
    (3, 3),
    (3, 4),
    (3, 5),
    (3, 6),
    (3, 7),
    (3, 8),
    (3, 9),
    (3, 10),
    (3, 11),
    (4, 4),
    (4, 5),
    (4, 6),
    (4, 7),
    (4, 8),
    (4, 9),
    (4, 10),
    (4, 11),
    (5, 5),
    (5, 6),
    (5, 7),
    (5, 8),
    (5, 9),
    (5, 10),
    (5, 11),
    (6, 6),
    (6, 7),
    (6, 8),
    (6, 9),
    (6, 10),
    (6, 11),
    (7, 7),
    (7, 8),
    (7, 9),
    (7, 10),
    (7, 11),
    (8, 8),
    (8, 9),
    (8, 10),
    (8, 11),
    (9, 9),
    (9, 10),
    (9, 11),
    (10, 10),
    (10, 11),
    (11, 11)]

/-- Original row labels in the 680-row cubic matrix, in pivot order. -/
def cubicPivotRows : Fin 288 → Fin 680 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
    30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 120,
    45, 46, 47, 48, 49, 55, 51, 52, 53, 54, 50, 56, 57, 121, 122,
    60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 123, 124, 134,
    75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 125, 126, 135, 136,
    90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 127, 128, 137, 138, 147,
    105, 106, 107, 108, 109, 110, 111, 112, 113, 129, 130, 139, 140, 148, 149,
    59, 86, 100, 101, 131, 102, 103, 141, 104, 153, 164, 174, 183, 191, 198,
    88, 89, 58, 87, 116, 117, 142, 143, 154, 205, 165, 175, 184, 192, 199,
    150, 151, 152, 114, 44, 155, 156, 157, 158, 204, 210, 161, 162, 163, 115,
    145, 166, 167, 168, 169, 170, 171, 172, 173, 206, 211, 176, 177, 178, 179,
    180, 181, 182, 132, 72, 185, 186, 187, 188, 207, 212, 133, 118, 193, 194,
    195, 196, 197, 74, 119, 200, 201, 202, 203, 208, 213, 73, 189, 159, 209,
    160, 146, 246, 144, 214, 247, 216, 217, 248, 219, 220, 249, 222, 223, 239,
    225, 234, 257, 235, 236, 258, 237, 224, 259, 240, 241, 260, 242, 243, 244,
    245, 190, 215, 218, 221, 276, 251, 252, 277, 253, 254, 278, 255, 256, 279,
    262, 263, 264, 265, 266, 284, 272, 273, 285, 274, 275, 286, 281, 282, 287,
    283, 289, 297, 290, 296, 298, 299, 300, 302, 303, 304, 305, 307, 308, 309,
    311, 312, 314]

/-- The cubic monomials at the selected rows. -/
def cubicPivotTuple : Fin 288 → Fin 15 × Fin 15 × Fin 15 :=
  ![(0, 0, 0),
    (0, 0, 1),
    (0, 0, 2),
    (0, 0, 3),
    (0, 0, 4),
    (0, 0, 5),
    (0, 0, 6),
    (0, 0, 7),
    (0, 0, 8),
    (0, 0, 9),
    (0, 0, 10),
    (0, 0, 11),
    (0, 0, 12),
    (0, 0, 13),
    (0, 0, 14),
    (0, 1, 1),
    (0, 1, 2),
    (0, 1, 3),
    (0, 1, 4),
    (0, 1, 5),
    (0, 1, 6),
    (0, 1, 7),
    (0, 1, 8),
    (0, 1, 9),
    (0, 1, 10),
    (0, 1, 11),
    (0, 1, 12),
    (0, 1, 13),
    (0, 1, 14),
    (0, 2, 2),
    (0, 2, 3),
    (0, 2, 4),
    (0, 2, 5),
    (0, 2, 6),
    (0, 2, 7),
    (0, 2, 8),
    (0, 2, 9),
    (0, 2, 10),
    (0, 2, 11),
    (0, 2, 12),
    (0, 2, 13),
    (0, 2, 14),
    (0, 3, 3),
    (0, 3, 4),
    (1, 1, 1),
    (0, 3, 6),
    (0, 3, 7),
    (0, 3, 8),
    (0, 3, 9),
    (0, 3, 10),
    (0, 4, 5),
    (0, 3, 12),
    (0, 3, 13),
    (0, 3, 14),
    (0, 4, 4),
    (0, 3, 11),
    (0, 4, 6),
    (0, 4, 7),
    (1, 1, 2),
    (1, 1, 3),
    (0, 4, 10),
    (0, 4, 11),
    (0, 4, 12),
    (0, 4, 13),
    (0, 4, 14),
    (0, 5, 5),
    (0, 5, 6),
    (0, 5, 7),
    (0, 5, 8),
    (0, 5, 9),
    (0, 5, 10),
    (0, 5, 11),
    (1, 1, 4),
    (1, 1, 5),
    (1, 2, 2),
    (0, 6, 6),
    (0, 6, 7),
    (0, 6, 8),
    (0, 6, 9),
    (0, 6, 10),
    (0, 6, 11),
    (0, 6, 12),
    (0, 6, 13),
    (0, 6, 14),
    (0, 7, 7),
    (0, 7, 8),
    (1, 1, 6),
    (1, 1, 7),
    (1, 2, 3),
    (1, 2, 4),
    (0, 7, 13),
    (0, 7, 14),
    (0, 8, 8),
    (0, 8, 9),
    (0, 8, 10),
    (0, 8, 11),
    (0, 8, 12),
    (0, 8, 13),
    (0, 8, 14),
    (0, 9, 9),
    (1, 1, 8),
    (1, 1, 9),
    (1, 2, 5),
    (1, 2, 6),
    (1, 3, 3),
    (0, 10, 10),
    (0, 10, 11),
    (0, 10, 12),
    (0, 10, 13),
    (0, 10, 14),
    (0, 11, 11),
    (0, 11, 12),
    (0, 11, 13),
    (0, 11, 14),
    (1, 1, 10),
    (1, 1, 11),
    (1, 2, 7),
    (1, 2, 8),
    (1, 3, 4),
    (1, 3, 5),
    (0, 4, 9),
    (0, 7, 9),
    (0, 9, 10),
    (0, 9, 11),
    (1, 1, 12),
    (0, 9, 12),
    (0, 9, 13),
    (1, 2, 9),
    (0, 9, 14),
    (1, 3, 9),
    (1, 4, 9),
    (1, 5, 9),
    (1, 6, 9),
    (1, 7, 9),
    (1, 8, 9),
    (0, 7, 11),
    (0, 7, 12),
    (0, 4, 8),
    (0, 7, 10),
    (0, 12, 14),
    (0, 13, 13),
    (1, 2, 10),
    (1, 2, 11),
    (1, 3, 10),
    (1, 9, 10),
    (1, 4, 10),
    (1, 5, 10),
    (1, 6, 10),
    (1, 7, 10),
    (1, 8, 10),
    (1, 3, 6),
    (1, 3, 7),
    (1, 3, 8),
    (0, 12, 12),
    (0, 3, 5),
    (1, 3, 11),
    (1, 3, 12),
    (1, 3, 13),
    (1, 3, 14),
    (1, 9, 9),
    (1, 10, 10),
    (1, 4, 6),
    (1, 4, 7),
    (1, 4, 8),
    (0, 12, 13),
    (1, 2, 13),
    (1, 4, 11),
    (1, 4, 12),
    (1, 4, 13),
    (1, 4, 14),
    (1, 5, 5),
    (1, 5, 6),
    (1, 5, 7),
    (1, 5, 8),
    (1, 9, 11),
    (1, 10, 11),
    (1, 5, 11),
    (1, 5, 12),
    (1, 5, 13),
    (1, 5, 14),
    (1, 6, 6),
    (1, 6, 7),
    (1, 6, 8),
    (1, 1, 13),
    (0, 5, 12),
    (1, 6, 11),
    (1, 6, 12),
    (1, 6, 13),
    (1, 6, 14),
    (1, 9, 12),
    (1, 10, 12),
    (1, 1, 14),
    (0, 13, 14),
    (1, 7, 11),
    (1, 7, 12),
    (1, 7, 13),
    (1, 7, 14),
    (1, 8, 8),
    (0, 5, 14),
    (0, 14, 14),
    (1, 8, 11),
    (1, 8, 12),
    (1, 8, 13),
    (1, 8, 14),
    (1, 9, 13),
    (1, 10, 13),
    (0, 5, 13),
    (1, 7, 7),
    (1, 4, 4),
    (1, 9, 14),
    (1, 4, 5),
    (1, 2, 14),
    (2, 3, 11),
    (1, 2, 12),
    (1, 10, 14),
    (2, 3, 12),
    (1, 11, 12),
    (1, 11, 13),
    (2, 3, 13),
    (1, 12, 12),
    (1, 12, 13),
    (2, 3, 14),
    (1, 13, 13),
    (1, 13, 14),
    (2, 3, 4),
    (2, 2, 2),
    (2, 2, 11),
    (2, 4, 11),
    (2, 2, 12),
    (2, 2, 13),
    (2, 4, 12),
    (2, 2, 14),
    (1, 14, 14),
    (2, 4, 13),
    (2, 3, 5),
    (2, 3, 6),
    (2, 4, 14),
    (2, 3, 7),
    (2, 3, 8),
    (2, 3, 9),
    (2, 3, 10),
    (1, 7, 8),
    (1, 11, 11),
    (1, 11, 14),
    (1, 12, 14),
    (2, 6, 11),
    (2, 4, 5),
    (2, 4, 6),
    (2, 6, 12),
    (2, 4, 7),
    (2, 4, 8),
    (2, 6, 13),
    (2, 4, 9),
    (2, 4, 10),
    (2, 6, 14),
    (2, 5, 6),
    (2, 5, 7),
    (2, 5, 8),
    (2, 5, 9),
    (2, 5, 10),
    (2, 7, 11),
    (2, 6, 7),
    (2, 6, 8),
    (2, 7, 12),
    (2, 6, 9),
    (2, 6, 10),
    (2, 7, 13),
    (2, 7, 8),
    (2, 7, 9),
    (2, 7, 14),
    (2, 7, 10),
    (2, 8, 9),
    (2, 9, 11),
    (2, 8, 10),
    (2, 9, 10),
    (2, 9, 12),
    (2, 9, 13),
    (2, 9, 14),
    (2, 10, 11),
    (2, 10, 12),
    (2, 10, 13),
    (2, 10, 14),
    (2, 11, 12),
    (2, 11, 13),
    (2, 11, 14),
    (2, 12, 13),
    (2, 12, 14),
    (2, 13, 14)]

def normalPivots : Fin 28 → Fin 42 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def normalFree : Fin 14 → Fin 42 :=
  ![28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]

def tracePivots : Fin 52 → Fin 78 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 33,
    34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 50, 57, 58, 59,
    60, 61, 63, 68, 72, 75, 77]

def traceFree : Fin 26 → Fin 78 :=
  ![29, 30, 31, 32, 45, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56,
    62, 64, 65, 66, 67, 69, 70, 71, 73, 74, 76]

def normalColumn : Fin 28 ⊕ Fin 14 → Fin 42 := Sum.elim normalPivots normalFree

def traceColumn : Fin 52 ⊕ Fin 26 → Fin 78 := Sum.elim tracePivots traceFree

theorem normalColumn_bijective : Function.Bijective normalColumn := by decide +kernel

theorem traceColumn_bijective : Function.Bijective traceColumn := by decide +kernel

def normalExponentLex (j : Fin 42) : Fin 15 →₀ ℕ :=
  Finsupp.single ((normalQuadraticTuple j).1.castAdd 12) 1 +
    Finsupp.single (normalQuadraticTuple j).2 1

def traceExponentLex (j : Fin 78) : Fin 12 →₀ ℕ :=
  Finsupp.single (traceQuadraticTuple j).1 1 + Finsupp.single (traceQuadraticTuple j).2 1

/-- Normal quadrics in pivot/free order for the kernel chart. -/
def normalExponent (j : Fin 28 ⊕ Fin 14) : Fin 15 →₀ ℕ :=
  normalExponentLex (normalColumn j)

/-- Trace quadrics in pivot/free order for the kernel chart. -/
def traceExponent (j : Fin 52 ⊕ Fin 26) : Fin 12 →₀ ℕ :=
  traceExponentLex (traceColumn j)

def cubicExponent (j : Fin 288) : Fin 15 →₀ ℕ :=
  let t := cubicPivotTuple j
  Finsupp.single t.1 1 + Finsupp.single t.2.1 1 + Finsupp.single t.2.2 1

theorem normalExponent_degree (j : Fin 28 ⊕ Fin 14) : (normalExponent j).degree = 2 := by
  simp [normalExponent, normalExponentLex, Finsupp.degree_single]

theorem traceExponent_degree (j : Fin 52 ⊕ Fin 26) : (traceExponent j).degree = 2 := by
  simp [traceExponent, traceExponentLex, Finsupp.degree_single]

theorem normalExponent_support (j : Fin 28 ⊕ Fin 14) :
    ∃ i : Fin 3, normalExponent j (i.castAdd 12) ≠ 0 := by
  refine ⟨(normalQuadraticTuple (normalColumn j)).1, ?_⟩
  simp [normalExponent, normalExponentLex, Finsupp.add_apply]

theorem sorted_pair_exponents_injective {n : ℕ} {a b u v : Fin n}
    (hab : a ≤ b) (huv : u ≤ v)
    (h : Finsupp.single a (1 : ℕ) + Finsupp.single b 1 =
      Finsupp.single u 1 + Finsupp.single v 1) : a = u ∧ b = v := by
  have hau : a = u := by
    apply le_antisymm
    · by_contra! hlt
      have he := congrArg (fun f : Fin n →₀ ℕ => f u) h
      have hbu : b ≠ u := ne_of_gt (hlt.trans_le hab)
      simp only [Finsupp.add_apply, Finsupp.single_apply, ne_of_gt hlt, hbu,
        ite_false, ite_true] at he
      omega
    · by_contra! hlt
      have he := congrArg (fun f : Fin n →₀ ℕ => f a) h
      have hva : v ≠ a := ne_of_gt (hlt.trans_le huv)
      simp only [Finsupp.add_apply, Finsupp.single_apply, ne_of_gt hlt, hva,
        ite_false, ite_true] at he
      omega
  subst u
  exact ⟨rfl, Finsupp.single_left_injective one_ne_zero (add_left_cancel h)⟩

private theorem normalQuadraticTuple_injective : Function.Injective normalQuadraticTuple := by
  decide +kernel

private theorem traceQuadraticTuple_injective : Function.Injective traceQuadraticTuple := by
  decide +kernel

private theorem normalQuadraticTuple_sorted : ∀ i,
    (normalQuadraticTuple i).1.castAdd 12 ≤ (normalQuadraticTuple i).2 := by
  decide +kernel

private theorem traceQuadraticTuple_sorted : ∀ i,
    (traceQuadraticTuple i).1 ≤ (traceQuadraticTuple i).2 := by
  decide +kernel

theorem normalExponentLex_injective : Function.Injective normalExponentLex := by
  intro i j h
  obtain ⟨h₁, h₂⟩ := sorted_pair_exponents_injective
    (normalQuadraticTuple_sorted i) (normalQuadraticTuple_sorted j) h
  exact normalQuadraticTuple_injective
    (Prod.ext (Fin.ext (congrArg (fun k : Fin 15 => k.val) h₁)) h₂)

theorem traceExponentLex_injective : Function.Injective traceExponentLex := by
  intro i j h
  obtain ⟨h₁, h₂⟩ := sorted_pair_exponents_injective
    (traceQuadraticTuple_sorted i) (traceQuadraticTuple_sorted j) h
  exact traceQuadraticTuple_injective (Prod.ext h₁ h₂)

theorem normalExponent_injective : Function.Injective normalExponent :=
  normalExponentLex_injective.comp normalColumn_bijective.1

theorem traceExponent_injective : Function.Injective traceExponent :=
  traceExponentLex_injective.comp traceColumn_bijective.1

end IdealGeneration.TripleNormalInitial
