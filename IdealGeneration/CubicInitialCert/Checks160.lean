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

theorem upper160 : packedUpper 160 =
    packSparse (2 ^ 40) (upperRows 160) := by decide +kernel

theorem packed160 : packedProduct (lowerRows 160) packedUpper =
    packSparse (2 ^ 40) (targetRows 160) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 160) := by decide +kernel

theorem rowFacts160 : PackedRowFacts 160 := by
  constructor <;> decide +kernel

theorem upper161 : packedUpper 161 =
    packSparse (2 ^ 40) (upperRows 161) := by decide +kernel

theorem packed161 : packedProduct (lowerRows 161) packedUpper =
    packSparse (2 ^ 40) (targetRows 161) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 161) := by decide +kernel

theorem rowFacts161 : PackedRowFacts 161 := by
  constructor <;> decide +kernel

theorem upper162 : packedUpper 162 =
    packSparse (2 ^ 40) (upperRows 162) := by decide +kernel

theorem packed162 : packedProduct (lowerRows 162) packedUpper =
    packSparse (2 ^ 40) (targetRows 162) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 162) := by decide +kernel

theorem rowFacts162 : PackedRowFacts 162 := by
  constructor <;> decide +kernel

theorem upper163 : packedUpper 163 =
    packSparse (2 ^ 40) (upperRows 163) := by decide +kernel

theorem packed163 : packedProduct (lowerRows 163) packedUpper =
    packSparse (2 ^ 40) (targetRows 163) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 163) := by decide +kernel

theorem rowFacts163 : PackedRowFacts 163 := by
  constructor <;> decide +kernel

theorem upper164 : packedUpper 164 =
    packSparse (2 ^ 40) (upperRows 164) := by decide +kernel

theorem packed164 : packedProduct (lowerRows 164) packedUpper =
    packSparse (2 ^ 40) (targetRows 164) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 164) := by decide +kernel

theorem rowFacts164 : PackedRowFacts 164 := by
  constructor <;> decide +kernel

theorem upper165 : packedUpper 165 =
    packSparse (2 ^ 40) (upperRows 165) := by decide +kernel

theorem packed165 : packedProduct (lowerRows 165) packedUpper =
    packSparse (2 ^ 40) (targetRows 165) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 165) := by decide +kernel

theorem rowFacts165 : PackedRowFacts 165 := by
  constructor <;> decide +kernel

theorem upper166 : packedUpper 166 =
    packSparse (2 ^ 40) (upperRows 166) := by decide +kernel

theorem packed166 : packedProduct (lowerRows 166) packedUpper =
    packSparse (2 ^ 40) (targetRows 166) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 166) := by decide +kernel

theorem rowFacts166 : PackedRowFacts 166 := by
  constructor <;> decide +kernel

theorem upper167 : packedUpper 167 =
    packSparse (2 ^ 40) (upperRows 167) := by decide +kernel

theorem packed167 : packedProduct (lowerRows 167) packedUpper =
    packSparse (2 ^ 40) (targetRows 167) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 167) := by decide +kernel

theorem rowFacts167 : PackedRowFacts 167 := by
  constructor <;> decide +kernel

theorem upper168 : packedUpper 168 =
    packSparse (2 ^ 40) (upperRows 168) := by decide +kernel

theorem packed168 : packedProduct (lowerRows 168) packedUpper =
    packSparse (2 ^ 40) (targetRows 168) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 168) := by decide +kernel

theorem rowFacts168 : PackedRowFacts 168 := by
  constructor <;> decide +kernel

theorem upper169 : packedUpper 169 =
    packSparse (2 ^ 40) (upperRows 169) := by decide +kernel

theorem packed169 : packedProduct (lowerRows 169) packedUpper =
    packSparse (2 ^ 40) (targetRows 169) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 169) := by decide +kernel

theorem rowFacts169 : PackedRowFacts 169 := by
  constructor <;> decide +kernel

theorem upper170 : packedUpper 170 =
    packSparse (2 ^ 40) (upperRows 170) := by decide +kernel

theorem packed170 : packedProduct (lowerRows 170) packedUpper =
    packSparse (2 ^ 40) (targetRows 170) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 170) := by decide +kernel

theorem rowFacts170 : PackedRowFacts 170 := by
  constructor <;> decide +kernel

theorem upper171 : packedUpper 171 =
    packSparse (2 ^ 40) (upperRows 171) := by decide +kernel

theorem packed171 : packedProduct (lowerRows 171) packedUpper =
    packSparse (2 ^ 40) (targetRows 171) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 171) := by decide +kernel

theorem rowFacts171 : PackedRowFacts 171 := by
  constructor <;> decide +kernel

theorem upper172 : packedUpper 172 =
    packSparse (2 ^ 40) (upperRows 172) := by decide +kernel

theorem packed172 : packedProduct (lowerRows 172) packedUpper =
    packSparse (2 ^ 40) (targetRows 172) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 172) := by decide +kernel

theorem rowFacts172 : PackedRowFacts 172 := by
  constructor <;> decide +kernel

theorem upper173 : packedUpper 173 =
    packSparse (2 ^ 40) (upperRows 173) := by decide +kernel

theorem packed173 : packedProduct (lowerRows 173) packedUpper =
    packSparse (2 ^ 40) (targetRows 173) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 173) := by decide +kernel

theorem rowFacts173 : PackedRowFacts 173 := by
  constructor <;> decide +kernel

theorem upper174 : packedUpper 174 =
    packSparse (2 ^ 40) (upperRows 174) := by decide +kernel

theorem packed174 : packedProduct (lowerRows 174) packedUpper =
    packSparse (2 ^ 40) (targetRows 174) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 174) := by decide +kernel

theorem rowFacts174 : PackedRowFacts 174 := by
  constructor <;> decide +kernel

theorem upper175 : packedUpper 175 =
    packSparse (2 ^ 40) (upperRows 175) := by decide +kernel

theorem packed175 : packedProduct (lowerRows 175) packedUpper =
    packSparse (2 ^ 40) (targetRows 175) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 175) := by decide +kernel

theorem rowFacts175 : PackedRowFacts 175 := by
  constructor <;> decide +kernel

theorem upper176 : packedUpper 176 =
    packSparse (2 ^ 40) (upperRows 176) := by decide +kernel

theorem packed176 : packedProduct (lowerRows 176) packedUpper =
    packSparse (2 ^ 40) (targetRows 176) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 176) := by decide +kernel

theorem rowFacts176 : PackedRowFacts 176 := by
  constructor <;> decide +kernel

theorem upper177 : packedUpper 177 =
    packSparse (2 ^ 40) (upperRows 177) := by decide +kernel

theorem packed177 : packedProduct (lowerRows 177) packedUpper =
    packSparse (2 ^ 40) (targetRows 177) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 177) := by decide +kernel

theorem rowFacts177 : PackedRowFacts 177 := by
  constructor <;> decide +kernel

theorem upper178 : packedUpper 178 =
    packSparse (2 ^ 40) (upperRows 178) := by decide +kernel

theorem packed178 : packedProduct (lowerRows 178) packedUpper =
    packSparse (2 ^ 40) (targetRows 178) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 178) := by decide +kernel

theorem rowFacts178 : PackedRowFacts 178 := by
  constructor <;> decide +kernel

theorem upper179 : packedUpper 179 =
    packSparse (2 ^ 40) (upperRows 179) := by decide +kernel

theorem packed179 : packedProduct (lowerRows 179) packedUpper =
    packSparse (2 ^ 40) (targetRows 179) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 179) := by decide +kernel

theorem rowFacts179 : PackedRowFacts 179 := by
  constructor <;> decide +kernel

theorem upper180 : packedUpper 180 =
    packSparse (2 ^ 40) (upperRows 180) := by decide +kernel

theorem packed180 : packedProduct (lowerRows 180) packedUpper =
    packSparse (2 ^ 40) (targetRows 180) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 180) := by decide +kernel

theorem rowFacts180 : PackedRowFacts 180 := by
  constructor <;> decide +kernel

theorem upper181 : packedUpper 181 =
    packSparse (2 ^ 40) (upperRows 181) := by decide +kernel

theorem packed181 : packedProduct (lowerRows 181) packedUpper =
    packSparse (2 ^ 40) (targetRows 181) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 181) := by decide +kernel

theorem rowFacts181 : PackedRowFacts 181 := by
  constructor <;> decide +kernel

theorem upper182 : packedUpper 182 =
    packSparse (2 ^ 40) (upperRows 182) := by decide +kernel

theorem packed182 : packedProduct (lowerRows 182) packedUpper =
    packSparse (2 ^ 40) (targetRows 182) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 182) := by decide +kernel

theorem rowFacts182 : PackedRowFacts 182 := by
  constructor <;> decide +kernel

theorem upper183 : packedUpper 183 =
    packSparse (2 ^ 40) (upperRows 183) := by decide +kernel

theorem packed183 : packedProduct (lowerRows 183) packedUpper =
    packSparse (2 ^ 40) (targetRows 183) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 183) := by decide +kernel

theorem rowFacts183 : PackedRowFacts 183 := by
  constructor <;> decide +kernel

theorem upper184 : packedUpper 184 =
    packSparse (2 ^ 40) (upperRows 184) := by decide +kernel

theorem packed184 : packedProduct (lowerRows 184) packedUpper =
    packSparse (2 ^ 40) (targetRows 184) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 184) := by decide +kernel

theorem rowFacts184 : PackedRowFacts 184 := by
  constructor <;> decide +kernel

theorem upper185 : packedUpper 185 =
    packSparse (2 ^ 40) (upperRows 185) := by decide +kernel

theorem packed185 : packedProduct (lowerRows 185) packedUpper =
    packSparse (2 ^ 40) (targetRows 185) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 185) := by decide +kernel

theorem rowFacts185 : PackedRowFacts 185 := by
  constructor <;> decide +kernel

theorem upper186 : packedUpper 186 =
    packSparse (2 ^ 40) (upperRows 186) := by decide +kernel

theorem packed186 : packedProduct (lowerRows 186) packedUpper =
    packSparse (2 ^ 40) (targetRows 186) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 186) := by decide +kernel

theorem rowFacts186 : PackedRowFacts 186 := by
  constructor <;> decide +kernel

theorem upper187 : packedUpper 187 =
    packSparse (2 ^ 40) (upperRows 187) := by decide +kernel

theorem packed187 : packedProduct (lowerRows 187) packedUpper =
    packSparse (2 ^ 40) (targetRows 187) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 187) := by decide +kernel

theorem rowFacts187 : PackedRowFacts 187 := by
  constructor <;> decide +kernel

theorem upper188 : packedUpper 188 =
    packSparse (2 ^ 40) (upperRows 188) := by decide +kernel

theorem packed188 : packedProduct (lowerRows 188) packedUpper =
    packSparse (2 ^ 40) (targetRows 188) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 188) := by decide +kernel

theorem rowFacts188 : PackedRowFacts 188 := by
  constructor <;> decide +kernel

theorem upper189 : packedUpper 189 =
    packSparse (2 ^ 40) (upperRows 189) := by decide +kernel

theorem packed189 : packedProduct (lowerRows 189) packedUpper =
    packSparse (2 ^ 40) (targetRows 189) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 189) := by decide +kernel

theorem rowFacts189 : PackedRowFacts 189 := by
  constructor <;> decide +kernel

theorem upper190 : packedUpper 190 =
    packSparse (2 ^ 40) (upperRows 190) := by decide +kernel

theorem packed190 : packedProduct (lowerRows 190) packedUpper =
    packSparse (2 ^ 40) (targetRows 190) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 190) := by decide +kernel

theorem rowFacts190 : PackedRowFacts 190 := by
  constructor <;> decide +kernel

theorem upper191 : packedUpper 191 =
    packSparse (2 ^ 40) (upperRows 191) := by decide +kernel

theorem packed191 : packedProduct (lowerRows 191) packedUpper =
    packSparse (2 ^ 40) (targetRows 191) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 191) := by decide +kernel

theorem rowFacts191 : PackedRowFacts 191 := by
  constructor <;> decide +kernel

#print axioms packed191

end CertifiedRank.C2.PackedCertificate
