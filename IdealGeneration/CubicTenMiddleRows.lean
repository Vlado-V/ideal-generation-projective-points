module

public import IdealGeneration.CubicTenShift
public import IdealGeneration.CubicTenNormalKernelCertificate
public import IdealGeneration.CubicTenTraceKernelCertificate
public import IdealGeneration.CubicTenMiddleCertificate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The selected coefficient matrix agrees with the sparse middle certificate. -/

noncomputable section
namespace IdealGeneration.CubicTen
open Matrix ConeMonomialChart CertifiedRank CubicTenPackedData
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

private def normalBasisNat (i : Fin 100) (j : Fin 25) : ℕ :=
  rowValue (KnRow i) (Fin.castLE (by decide) j)

private def traceBasisNat (i : Fin 120) (j : Fin 30) : ℕ :=
  rowValue (KtRow i) (Fin.castLE (by decide) j)

private theorem lookupNat_cast (i j : Fin 310) :
    ((lookupMiddleEntry (R := ℕ) normalBasisNat traceBasisNat i j : ℕ) : ZMod modulus) =
      lookupMiddleEntry Kn Kt i j := by
  unfold lookupMiddleEntry
  cases naturalColumn (permutedColumnIndex j) with
  | inl k =>
    simp only [Sum.elim_inl]
    cases normalLookup i k.1 with
    | none => exact Nat.cast_zero
    | some a => exact (Kn_apply a k.2).symm
  | inr k =>
    simp only [Sum.elim_inr]
    cases traceLookup i k.1 with
    | none => exact Nat.cast_zero
    | some a => exact (Kt_apply a k.2).symm

private abbrev Column := MiddleColumn 2 8 (Fin 25) (Fin 30)

private def inverseColumnTable : Table ℕ 9 :=
  (((((((((0, 72), (271, 0)), ((188, 0), (155, 0))), (((17, 85), (122, 0)), ((201, 0), (98, 0)))), ((((26, 47), (254, 0)), ((144, 0), (106, 0))), (((224, 90), (280, 0)), ((261, 0), (219, 0))))), (((((257, 60), (161, 0)), ((194, 0), (291, 0))), (((308, 88), (307, 0)), ((165, 0), (186, 0)))), ((((19, 77), (294, 0)), ((218, 0), (124, 0))), (((56, 0), (167, 0)), ((239, 0), (101, 0)))))), ((((((6, 57), (169, 0)), ((236, 0), (274, 0))), (((27, 92), (151, 0)), ((259, 0), (228, 0)))), ((((21, 61), (171, 0)), ((196, 0), (184, 0))), (((242, 4), (119, 0)), ((260, 0), (204, 0))))), (((((304, 44), (182, 0)), ((225, 0), (73, 0))), (((22, 53), (276, 0)), ((162, 0), (209, 0)))), ((((3, 50), (75, 0)), ((266, 0), (139, 0))), (((181, 0), (148, 0)), ((154, 0), (42, 0))))))), (((((((279, 79), (120, 0)), ((192, 0), (157, 0))), (((18, 63), (250, 0)), ((143, 0), (226, 0)))), ((((34, 84), (272, 0)), ((131, 0), (128, 0))), (((238, 67), (269, 0)), ((287, 0), (202, 0))))), (((((282, 82), (159, 0)), ((174, 0), (299, 0))), (((298, 51), (270, 0)), ((130, 0), (206, 0)))), ((((30, 49), (74, 0)), ((214, 0), (229, 0))), (((178, 0), (146, 0)), ((234, 0), (71, 0)))))), ((((((244, 91), (133, 0)), ((216, 0), (138, 0))), (((12, 66), (153, 0)), ((302, 0), (141, 0)))), ((((33, 1), (285, 0)), ((215, 0), (158, 0))), (((35, 0), (135, 0)), ((249, 0), (231, 0))))), (((((11, 46), (309, 0)), ((264, 0), (76, 0))), (((283, 54), (113, 0)), ((100, 0), (210, 0)))), ((((15, 78), (123, 0)), ((265, 0), (142, 0))), (((237, 0), (185, 0)), ((306, 0), (43, 0)))))))), ((((((((303, 111), (69, 0)), ((189, 0), (156, 0))), (((8, 86), (150, 0)), ((199, 0), (230, 0)))), ((((20, 38), (277, 0)), ((116, 0), (168, 0))), (((10, 55), (289, 0)), ((275, 0), (220, 0))))), (((((118, 81), (160, 0)), ((173, 0), (281, 0))), (((13, 115), (253, 0)), ((163, 0), (187, 0)))), ((((29, 96), (290, 0)), ((213, 0), (295, 0))), (((177, 0), (127, 0)), ((240, 0), (102, 0)))))), ((((((245, 58), (126, 0)), ((197, 0), (166, 0))), (((25, 65), (152, 0)), ((246, 0), (175, 0)))), ((((31, 62), (125, 0)), ((205, 0), (149, 0))), (((243, 5), (95, 0)), ((233, 0), (222, 0))))), (((((267, 45), (251, 0)), ((258, 0), (103, 0))), (((278, 89), (172, 0)), ((99, 0), (211, 0)))), ((((16, 40), (170, 0)), ((221, 0), (140, 0))), (((223, 0), (164, 0)), ((297, 0), (36, 0))))))), (((((((28, 80), (108, 0)), ((198, 0), (195, 0))), (((9, 64), (147, 0)), ((107, 0), (227, 0)))), ((((32, 48), (305, 0)), ((132, 0), (145, 0))), (((235, 68), (94, 0)), ((301, 0), (203, 0))))), (((((14, 112), (247, 0)), ((256, 0), (300, 0))), (((288, 52), (286, 0)), ((191, 0), (207, 0)))), ((((284, 39), (104, 0)), ((212, 0), (268, 0))), (((180, 0), (183, 0)), ((190, 0), (93, 0)))))), ((((((117, 59), (121, 0)), ((193, 0), (97, 0))), (((292, 87), (252, 0)), ((263, 0), (110, 0)))), ((((109, 2), (293, 0)), ((217, 0), (179, 0))), (((70, 0), (105, 0)), ((248, 0), (232, 0))))), (((((24, 83), (255, 0)), ((176, 0), (137, 0))), (((23, 41), (296, 0)), ((262, 0), (208, 0)))), ((((7, 114), (134, 0)), ((200, 0), (136, 0))), (((241, 0), (129, 0)), ((273, 0), (37, 0)))))))))

private def inverseColumnIndex (j : Fin 310) : Fin 310 :=
  Fin.ofNat 310 (tableGet 9 inverseColumnTable j.val)

private theorem columnIndex_inverse :
    ∀ j : Fin 310, permutedColumnIndex (inverseColumnIndex j) = j := by decide +kernel

private def columnPosition (a : Column) : Fin 310 := inverseColumnIndex (naturalColumn.symm a)

private theorem columnPosition_eq (a : Column) : columnPosition a = permutedColumn.symm a := by
  apply permutedColumn.injective
  change naturalColumn (permutedColumnIndex (inverseColumnIndex (naturalColumn.symm a))) =
    permutedColumn (permutedColumn.symm a)
  simp only [columnIndex_inverse, Equiv.apply_symm_apply]

private def group {b : ℕ} {V : Type*} (index : Fin b → Fin 310)
    (entry : V → Fin b → ℕ) (pred : Option V) : SparseRow 310 ℕ :=
  match pred with
  | none => []
  | some a => (List.ofFn fun k => (index k, entry a k)).filter fun e => e.2 != 0

private theorem rowValue_filter_nonzero (l : SparseRow 310 ℕ) (j : Fin 310) :
    rowValue (l.filter fun e => e.2 != 0) j = rowValue l j := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [rowValue] at ih
    by_cases h : e.2 = 0 <;> simp [h, rowValue, ih]

private theorem group_rowValue {b : ℕ} {V : Type*} (index : Fin b → Fin 310)
    (entry : V → Fin b → ℕ) (pred : Option V) (j : Fin 310) :
    rowValue (group index entry pred) j =
      ∑ k, if index k = j then ((pred.map fun a => entry a k).getD 0) else 0 := by
  cases pred with
  | none => simp [group, rowValue]
  | some a =>
    rw [group, rowValue_filter_nonzero]
    simp only [rowValue, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
      Option.map_some, Option.getD_some]

private theorem rowValue_flatten (rows : List (SparseRow 310 ℕ)) (j : Fin 310) :
    rowValue rows.flatten j = (rows.map fun row => rowValue row j).sum := by
  induction rows with
  | nil => rfl
  | cons r rs ih => simp [List.flatten_cons, rowValue_append, ih]

def rawSparseMiddleRow (i : Fin 310) : SparseRow 310 ℕ :=
  (List.ofFn fun j : Fin 10 =>
    group (fun k => columnPosition (.inl (j, k))) normalBasisNat (normalLookup i j)).flatten ++
  (List.ofFn fun j : Fin 2 =>
    group (fun k => columnPosition (.inr (j, k))) traceBasisNat (traceLookup i j)).flatten

private def unpermutedMiddleEntry (i : Fin 310) (a : Column) : ℕ :=
  Sum.elim (fun k => ((normalLookup i k.1).map (fun b => normalBasisNat b k.2)).getD 0)
    (fun k => ((traceLookup i k.1).map (fun b => traceBasisNat b k.2)).getD 0) a

private theorem rowValue_rawSparseMiddleRow (i j : Fin 310) :
    rowValue (rawSparseMiddleRow i) j = lookupMiddleEntry normalBasisNat traceBasisNat i j := by
  classical
  have hsum :
      rowValue (rawSparseMiddleRow i) j =
        ∑ a : Column, if columnPosition a = j then unpermutedMiddleEntry i a else 0 := by
    rw [rawSparseMiddleRow, rowValue_append, rowValue_flatten, rowValue_flatten]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, group_rowValue,
      Fintype.sum_sum_type, Fintype.sum_prod_type, unpermutedMiddleEntry, Sum.elim_inl, Sum.elim_inr]
  have hindex (a : Column) : columnPosition a = j ↔ a = permutedColumn j := by
    rw [columnPosition_eq]
    constructor
    · intro h
      exact (permutedColumn.apply_symm_apply a).symm.trans (congrArg permutedColumn h)
    · intro h
      rw [h, Equiv.symm_apply_apply]
  rw [hsum]
  simp_rw [hindex]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change unpermutedMiddleEntry i (naturalColumn (permutedColumnIndex j)) = _
  rfl

theorem middleEntry_of_agreement (i j : Fin 310)
    (hr : (rawSparseMiddleRow i).Perm (MRow i)) :
    middleMatrix normalExponent traceExponent quarticExponent Kn Kt i (permutedColumn j) =
      targetM i j := by
  rw [middleMatrix_eq_lookup, targetM_apply, ← lookupNat_cast, ← rowValue_rawSparseMiddleRow]
  have hsum : rowValue (rawSparseMiddleRow i) j = rowValue (MRow i) j := by
    unfold rowValue
    exact (hr.map (fun e : Fin 310 × ℕ => if e.1 = j then e.2 else 0)).sum_eq
  exact congrArg (fun x : ℕ => (x : ZMod modulus)) hsum

end IdealGeneration.CubicTen
