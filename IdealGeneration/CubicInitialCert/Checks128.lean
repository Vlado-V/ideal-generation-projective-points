module

public import IdealGeneration.CubicInitialCert.CheckDefinitions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedRank.C2.PackedCertificate

theorem upper128 : packedUpper 128 =
    packSparse (2 ^ 40) (upperRows 128) := by decide +kernel

theorem packed128 : packedProduct (lowerRows 128) packedUpper =
    packSparse (2 ^ 40) (targetRows 128) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 128) := by decide +kernel

theorem rowFacts128 : PackedRowFacts 128 := by
  constructor <;> decide +kernel

theorem upper129 : packedUpper 129 =
    packSparse (2 ^ 40) (upperRows 129) := by decide +kernel

theorem packed129 : packedProduct (lowerRows 129) packedUpper =
    packSparse (2 ^ 40) (targetRows 129) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 129) := by decide +kernel

theorem rowFacts129 : PackedRowFacts 129 := by
  constructor <;> decide +kernel

theorem upper130 : packedUpper 130 =
    packSparse (2 ^ 40) (upperRows 130) := by decide +kernel

theorem packed130 : packedProduct (lowerRows 130) packedUpper =
    packSparse (2 ^ 40) (targetRows 130) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 130) := by decide +kernel

theorem rowFacts130 : PackedRowFacts 130 := by
  constructor <;> decide +kernel

theorem upper131 : packedUpper 131 =
    packSparse (2 ^ 40) (upperRows 131) := by decide +kernel

theorem packed131 : packedProduct (lowerRows 131) packedUpper =
    packSparse (2 ^ 40) (targetRows 131) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 131) := by decide +kernel

theorem rowFacts131 : PackedRowFacts 131 := by
  constructor <;> decide +kernel

theorem upper132 : packedUpper 132 =
    packSparse (2 ^ 40) (upperRows 132) := by decide +kernel

theorem packed132 : packedProduct (lowerRows 132) packedUpper =
    packSparse (2 ^ 40) (targetRows 132) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 132) := by decide +kernel

theorem rowFacts132 : PackedRowFacts 132 := by
  constructor <;> decide +kernel

theorem upper133 : packedUpper 133 =
    packSparse (2 ^ 40) (upperRows 133) := by decide +kernel

theorem packed133 : packedProduct (lowerRows 133) packedUpper =
    packSparse (2 ^ 40) (targetRows 133) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 133) := by decide +kernel

theorem rowFacts133 : PackedRowFacts 133 := by
  constructor <;> decide +kernel

theorem upper134 : packedUpper 134 =
    packSparse (2 ^ 40) (upperRows 134) := by decide +kernel

theorem packed134 : packedProduct (lowerRows 134) packedUpper =
    packSparse (2 ^ 40) (targetRows 134) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 134) := by decide +kernel

theorem rowFacts134 : PackedRowFacts 134 := by
  constructor <;> decide +kernel

theorem upper135 : packedUpper 135 =
    packSparse (2 ^ 40) (upperRows 135) := by decide +kernel

theorem packed135 : packedProduct (lowerRows 135) packedUpper =
    packSparse (2 ^ 40) (targetRows 135) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 135) := by decide +kernel

theorem rowFacts135 : PackedRowFacts 135 := by
  constructor <;> decide +kernel

theorem upper136 : packedUpper 136 =
    packSparse (2 ^ 40) (upperRows 136) := by decide +kernel

theorem packed136 : packedProduct (lowerRows 136) packedUpper =
    packSparse (2 ^ 40) (targetRows 136) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 136) := by decide +kernel

theorem rowFacts136 : PackedRowFacts 136 := by
  constructor <;> decide +kernel

theorem upper137 : packedUpper 137 =
    packSparse (2 ^ 40) (upperRows 137) := by decide +kernel

theorem packed137 : packedProduct (lowerRows 137) packedUpper =
    packSparse (2 ^ 40) (targetRows 137) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 137) := by decide +kernel

theorem rowFacts137 : PackedRowFacts 137 := by
  constructor <;> decide +kernel

theorem upper138 : packedUpper 138 =
    packSparse (2 ^ 40) (upperRows 138) := by decide +kernel

theorem packed138 : packedProduct (lowerRows 138) packedUpper =
    packSparse (2 ^ 40) (targetRows 138) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 138) := by decide +kernel

theorem rowFacts138 : PackedRowFacts 138 := by
  constructor <;> decide +kernel

theorem upper139 : packedUpper 139 =
    packSparse (2 ^ 40) (upperRows 139) := by decide +kernel

theorem packed139 : packedProduct (lowerRows 139) packedUpper =
    packSparse (2 ^ 40) (targetRows 139) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 139) := by decide +kernel

theorem rowFacts139 : PackedRowFacts 139 := by
  constructor <;> decide +kernel

theorem upper140 : packedUpper 140 =
    packSparse (2 ^ 40) (upperRows 140) := by decide +kernel

theorem packed140 : packedProduct (lowerRows 140) packedUpper =
    packSparse (2 ^ 40) (targetRows 140) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 140) := by decide +kernel

theorem rowFacts140 : PackedRowFacts 140 := by
  constructor <;> decide +kernel

theorem upper141 : packedUpper 141 =
    packSparse (2 ^ 40) (upperRows 141) := by decide +kernel

theorem packed141 : packedProduct (lowerRows 141) packedUpper =
    packSparse (2 ^ 40) (targetRows 141) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 141) := by decide +kernel

theorem rowFacts141 : PackedRowFacts 141 := by
  constructor <;> decide +kernel

theorem upper142 : packedUpper 142 =
    packSparse (2 ^ 40) (upperRows 142) := by decide +kernel

theorem packed142 : packedProduct (lowerRows 142) packedUpper =
    packSparse (2 ^ 40) (targetRows 142) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 142) := by decide +kernel

theorem rowFacts142 : PackedRowFacts 142 := by
  constructor <;> decide +kernel

theorem upper143 : packedUpper 143 =
    packSparse (2 ^ 40) (upperRows 143) := by decide +kernel

theorem packed143 : packedProduct (lowerRows 143) packedUpper =
    packSparse (2 ^ 40) (targetRows 143) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 143) := by decide +kernel

theorem rowFacts143 : PackedRowFacts 143 := by
  constructor <;> decide +kernel

theorem upper144 : packedUpper 144 =
    packSparse (2 ^ 40) (upperRows 144) := by decide +kernel

theorem packed144 : packedProduct (lowerRows 144) packedUpper =
    packSparse (2 ^ 40) (targetRows 144) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 144) := by decide +kernel

theorem rowFacts144 : PackedRowFacts 144 := by
  constructor <;> decide +kernel

theorem upper145 : packedUpper 145 =
    packSparse (2 ^ 40) (upperRows 145) := by decide +kernel

theorem packed145 : packedProduct (lowerRows 145) packedUpper =
    packSparse (2 ^ 40) (targetRows 145) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 145) := by decide +kernel

theorem rowFacts145 : PackedRowFacts 145 := by
  constructor <;> decide +kernel

theorem upper146 : packedUpper 146 =
    packSparse (2 ^ 40) (upperRows 146) := by decide +kernel

theorem packed146 : packedProduct (lowerRows 146) packedUpper =
    packSparse (2 ^ 40) (targetRows 146) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 146) := by decide +kernel

theorem rowFacts146 : PackedRowFacts 146 := by
  constructor <;> decide +kernel

theorem upper147 : packedUpper 147 =
    packSparse (2 ^ 40) (upperRows 147) := by decide +kernel

theorem packed147 : packedProduct (lowerRows 147) packedUpper =
    packSparse (2 ^ 40) (targetRows 147) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 147) := by decide +kernel

theorem rowFacts147 : PackedRowFacts 147 := by
  constructor <;> decide +kernel

theorem upper148 : packedUpper 148 =
    packSparse (2 ^ 40) (upperRows 148) := by decide +kernel

theorem packed148 : packedProduct (lowerRows 148) packedUpper =
    packSparse (2 ^ 40) (targetRows 148) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 148) := by decide +kernel

theorem rowFacts148 : PackedRowFacts 148 := by
  constructor <;> decide +kernel

theorem upper149 : packedUpper 149 =
    packSparse (2 ^ 40) (upperRows 149) := by decide +kernel

theorem packed149 : packedProduct (lowerRows 149) packedUpper =
    packSparse (2 ^ 40) (targetRows 149) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 149) := by decide +kernel

theorem rowFacts149 : PackedRowFacts 149 := by
  constructor <;> decide +kernel

theorem upper150 : packedUpper 150 =
    packSparse (2 ^ 40) (upperRows 150) := by decide +kernel

theorem packed150 : packedProduct (lowerRows 150) packedUpper =
    packSparse (2 ^ 40) (targetRows 150) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 150) := by decide +kernel

theorem rowFacts150 : PackedRowFacts 150 := by
  constructor <;> decide +kernel

theorem upper151 : packedUpper 151 =
    packSparse (2 ^ 40) (upperRows 151) := by decide +kernel

theorem packed151 : packedProduct (lowerRows 151) packedUpper =
    packSparse (2 ^ 40) (targetRows 151) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 151) := by decide +kernel

theorem rowFacts151 : PackedRowFacts 151 := by
  constructor <;> decide +kernel

theorem upper152 : packedUpper 152 =
    packSparse (2 ^ 40) (upperRows 152) := by decide +kernel

theorem packed152 : packedProduct (lowerRows 152) packedUpper =
    packSparse (2 ^ 40) (targetRows 152) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 152) := by decide +kernel

theorem rowFacts152 : PackedRowFacts 152 := by
  constructor <;> decide +kernel

theorem upper153 : packedUpper 153 =
    packSparse (2 ^ 40) (upperRows 153) := by decide +kernel

theorem packed153 : packedProduct (lowerRows 153) packedUpper =
    packSparse (2 ^ 40) (targetRows 153) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 153) := by decide +kernel

theorem rowFacts153 : PackedRowFacts 153 := by
  constructor <;> decide +kernel

theorem upper154 : packedUpper 154 =
    packSparse (2 ^ 40) (upperRows 154) := by decide +kernel

theorem packed154 : packedProduct (lowerRows 154) packedUpper =
    packSparse (2 ^ 40) (targetRows 154) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 154) := by decide +kernel

theorem rowFacts154 : PackedRowFacts 154 := by
  constructor <;> decide +kernel

theorem upper155 : packedUpper 155 =
    packSparse (2 ^ 40) (upperRows 155) := by decide +kernel

theorem packed155 : packedProduct (lowerRows 155) packedUpper =
    packSparse (2 ^ 40) (targetRows 155) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 155) := by decide +kernel

theorem rowFacts155 : PackedRowFacts 155 := by
  constructor <;> decide +kernel

theorem upper156 : packedUpper 156 =
    packSparse (2 ^ 40) (upperRows 156) := by decide +kernel

theorem packed156 : packedProduct (lowerRows 156) packedUpper =
    packSparse (2 ^ 40) (targetRows 156) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 156) := by decide +kernel

theorem rowFacts156 : PackedRowFacts 156 := by
  constructor <;> decide +kernel

theorem upper157 : packedUpper 157 =
    packSparse (2 ^ 40) (upperRows 157) := by decide +kernel

theorem packed157 : packedProduct (lowerRows 157) packedUpper =
    packSparse (2 ^ 40) (targetRows 157) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 157) := by decide +kernel

theorem rowFacts157 : PackedRowFacts 157 := by
  constructor <;> decide +kernel

theorem upper158 : packedUpper 158 =
    packSparse (2 ^ 40) (upperRows 158) := by decide +kernel

theorem packed158 : packedProduct (lowerRows 158) packedUpper =
    packSparse (2 ^ 40) (targetRows 158) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 158) := by decide +kernel

theorem rowFacts158 : PackedRowFacts 158 := by
  constructor <;> decide +kernel

theorem upper159 : packedUpper 159 =
    packSparse (2 ^ 40) (upperRows 159) := by decide +kernel

theorem packed159 : packedProduct (lowerRows 159) packedUpper =
    packSparse (2 ^ 40) (targetRows 159) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 159) := by decide +kernel

theorem rowFacts159 : PackedRowFacts 159 := by
  constructor <;> decide +kernel

#print axioms packed159

end CertifiedRank.C2.PackedCertificate
