module

public import IdealGeneration.CubicRootCert.Checks000
public import IdealGeneration.CubicRootCert.Checks032
public import IdealGeneration.CubicRootCert.Checks064
public import IdealGeneration.CubicRootCert.Checks096
public import IdealGeneration.CubicRootCert.Checks128
public import Mathlib.Data.List.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace IdealGeneration.CubicSupported.C2RootCertificate

open CertifiedRank

private theorem forall_fin_of_rows {n : Nat} [NeZero n] {P : Fin n → Prop}
    (h : List.Forall (fun j => P (Fin.ofNat n j)) (List.range n)) : ∀ i, P i := by
  intro i
  have hi : Fin.ofNat n i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  exact hi ▸ (List.forall_iff_forall_mem.mp h i.val (List.mem_range.mpr i.isLt))

theorem packed_upper_rows : ∀ i, packedUpper i = packSparse (2 ^ 40) (upperRows i) := by
  refine forall_fin_of_rows (n := 160) ?_
  exact ⟨
    upper000, upper001, upper002, upper003, upper004, upper005, upper006, upper007,
    upper008, upper009, upper010, upper011, upper012, upper013, upper014, upper015,
    upper016, upper017, upper018, upper019, upper020, upper021, upper022, upper023,
    upper024, upper025, upper026, upper027, upper028, upper029, upper030, upper031,
    upper032, upper033, upper034, upper035, upper036, upper037, upper038, upper039,
    upper040, upper041, upper042, upper043, upper044, upper045, upper046, upper047,
    upper048, upper049, upper050, upper051, upper052, upper053, upper054, upper055,
    upper056, upper057, upper058, upper059, upper060, upper061, upper062, upper063,
    upper064, upper065, upper066, upper067, upper068, upper069, upper070, upper071,
    upper072, upper073, upper074, upper075, upper076, upper077, upper078, upper079,
    upper080, upper081, upper082, upper083, upper084, upper085, upper086, upper087,
    upper088, upper089, upper090, upper091, upper092, upper093, upper094, upper095,
    upper096, upper097, upper098, upper099, upper100, upper101, upper102, upper103,
    upper104, upper105, upper106, upper107, upper108, upper109, upper110, upper111,
    upper112, upper113, upper114, upper115, upper116, upper117, upper118, upper119,
    upper120, upper121, upper122, upper123, upper124, upper125, upper126, upper127,
    upper128, upper129, upper130, upper131, upper132, upper133, upper134, upper135,
    upper136, upper137, upper138, upper139, upper140, upper141, upper142, upper143,
    upper144, upper145, upper146, upper147, upper148, upper149, upper150, upper151,
    upper152, upper153, upper154, upper155, upper156, upper157, upper158, upper159
  ⟩

theorem packed_checks : ∀ i, packedProduct (lowerRows i) packedUpper =
    packSparse (2 ^ 40) (targetRows i) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows i) := by
  refine forall_fin_of_rows (n := 160) ?_
  exact ⟨
    packed000, packed001, packed002, packed003, packed004, packed005, packed006, packed007,
    packed008, packed009, packed010, packed011, packed012, packed013, packed014, packed015,
    packed016, packed017, packed018, packed019, packed020, packed021, packed022, packed023,
    packed024, packed025, packed026, packed027, packed028, packed029, packed030, packed031,
    packed032, packed033, packed034, packed035, packed036, packed037, packed038, packed039,
    packed040, packed041, packed042, packed043, packed044, packed045, packed046, packed047,
    packed048, packed049, packed050, packed051, packed052, packed053, packed054, packed055,
    packed056, packed057, packed058, packed059, packed060, packed061, packed062, packed063,
    packed064, packed065, packed066, packed067, packed068, packed069, packed070, packed071,
    packed072, packed073, packed074, packed075, packed076, packed077, packed078, packed079,
    packed080, packed081, packed082, packed083, packed084, packed085, packed086, packed087,
    packed088, packed089, packed090, packed091, packed092, packed093, packed094, packed095,
    packed096, packed097, packed098, packed099, packed100, packed101, packed102, packed103,
    packed104, packed105, packed106, packed107, packed108, packed109, packed110, packed111,
    packed112, packed113, packed114, packed115, packed116, packed117, packed118, packed119,
    packed120, packed121, packed122, packed123, packed124, packed125, packed126, packed127,
    packed128, packed129, packed130, packed131, packed132, packed133, packed134, packed135,
    packed136, packed137, packed138, packed139, packed140, packed141, packed142, packed143,
    packed144, packed145, packed146, packed147, packed148, packed149, packed150, packed151,
    packed152, packed153, packed154, packed155, packed156, packed157, packed158, packed159
  ⟩

theorem row_facts : ∀ i, PackedRowFacts i := by
  refine forall_fin_of_rows (n := 160) ?_
  exact ⟨
    rowFacts000, rowFacts001, rowFacts002, rowFacts003, rowFacts004, rowFacts005, rowFacts006, rowFacts007,
    rowFacts008, rowFacts009, rowFacts010, rowFacts011, rowFacts012, rowFacts013, rowFacts014, rowFacts015,
    rowFacts016, rowFacts017, rowFacts018, rowFacts019, rowFacts020, rowFacts021, rowFacts022, rowFacts023,
    rowFacts024, rowFacts025, rowFacts026, rowFacts027, rowFacts028, rowFacts029, rowFacts030, rowFacts031,
    rowFacts032, rowFacts033, rowFacts034, rowFacts035, rowFacts036, rowFacts037, rowFacts038, rowFacts039,
    rowFacts040, rowFacts041, rowFacts042, rowFacts043, rowFacts044, rowFacts045, rowFacts046, rowFacts047,
    rowFacts048, rowFacts049, rowFacts050, rowFacts051, rowFacts052, rowFacts053, rowFacts054, rowFacts055,
    rowFacts056, rowFacts057, rowFacts058, rowFacts059, rowFacts060, rowFacts061, rowFacts062, rowFacts063,
    rowFacts064, rowFacts065, rowFacts066, rowFacts067, rowFacts068, rowFacts069, rowFacts070, rowFacts071,
    rowFacts072, rowFacts073, rowFacts074, rowFacts075, rowFacts076, rowFacts077, rowFacts078, rowFacts079,
    rowFacts080, rowFacts081, rowFacts082, rowFacts083, rowFacts084, rowFacts085, rowFacts086, rowFacts087,
    rowFacts088, rowFacts089, rowFacts090, rowFacts091, rowFacts092, rowFacts093, rowFacts094, rowFacts095,
    rowFacts096, rowFacts097, rowFacts098, rowFacts099, rowFacts100, rowFacts101, rowFacts102, rowFacts103,
    rowFacts104, rowFacts105, rowFacts106, rowFacts107, rowFacts108, rowFacts109, rowFacts110, rowFacts111,
    rowFacts112, rowFacts113, rowFacts114, rowFacts115, rowFacts116, rowFacts117, rowFacts118, rowFacts119,
    rowFacts120, rowFacts121, rowFacts122, rowFacts123, rowFacts124, rowFacts125, rowFacts126, rowFacts127,
    rowFacts128, rowFacts129, rowFacts130, rowFacts131, rowFacts132, rowFacts133, rowFacts134, rowFacts135,
    rowFacts136, rowFacts137, rowFacts138, rowFacts139, rowFacts140, rowFacts141, rowFacts142, rowFacts143,
    rowFacts144, rowFacts145, rowFacts146, rowFacts147, rowFacts148, rowFacts149, rowFacts150, rowFacts151,
    rowFacts152, rowFacts153, rowFacts154, rowFacts155, rowFacts156, rowFacts157, rowFacts158, rowFacts159
  ⟩


end IdealGeneration.CubicSupported.C2RootCertificate
