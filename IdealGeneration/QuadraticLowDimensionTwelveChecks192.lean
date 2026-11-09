module

public import IdealGeneration.QuadraticLowDimensionTwelveData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact arithmetic checks for rows 192–287 of the twelve-variable certificate. -/

noncomputable section
namespace IdealGeneration.QuadraticLowDimension
open CertifiedRank
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024


theorem twelve_packed_row_192 :
    twelvePackedRows 192 = packedMinorResidueRow twelveMinor 2 1024 192 := by rfl

theorem twelve_packed_product_192 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 192) twelvePackedRows =
      1024 ^ (192 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 192) := by rfl

theorem twelve_packed_row_193 :
    twelvePackedRows 193 = packedMinorResidueRow twelveMinor 2 1024 193 := by rfl

theorem twelve_packed_product_193 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 193) twelvePackedRows =
      1024 ^ (193 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 193) := by rfl

theorem twelve_packed_row_194 :
    twelvePackedRows 194 = packedMinorResidueRow twelveMinor 2 1024 194 := by rfl

theorem twelve_packed_product_194 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 194) twelvePackedRows =
      1024 ^ (194 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 194) := by rfl

theorem twelve_packed_row_195 :
    twelvePackedRows 195 = packedMinorResidueRow twelveMinor 2 1024 195 := by rfl

theorem twelve_packed_product_195 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 195) twelvePackedRows =
      1024 ^ (195 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 195) := by rfl

theorem twelve_packed_row_196 :
    twelvePackedRows 196 = packedMinorResidueRow twelveMinor 2 1024 196 := by rfl

theorem twelve_packed_product_196 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 196) twelvePackedRows =
      1024 ^ (196 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 196) := by rfl

theorem twelve_packed_row_197 :
    twelvePackedRows 197 = packedMinorResidueRow twelveMinor 2 1024 197 := by rfl

theorem twelve_packed_product_197 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 197) twelvePackedRows =
      1024 ^ (197 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 197) := by rfl

theorem twelve_packed_row_198 :
    twelvePackedRows 198 = packedMinorResidueRow twelveMinor 2 1024 198 := by rfl

theorem twelve_packed_product_198 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 198) twelvePackedRows =
      1024 ^ (198 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 198) := by rfl

theorem twelve_packed_row_199 :
    twelvePackedRows 199 = packedMinorResidueRow twelveMinor 2 1024 199 := by rfl

theorem twelve_packed_product_199 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 199) twelvePackedRows =
      1024 ^ (199 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 199) := by rfl

theorem twelve_packed_row_200 :
    twelvePackedRows 200 = packedMinorResidueRow twelveMinor 2 1024 200 := by rfl

theorem twelve_packed_product_200 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 200) twelvePackedRows =
      1024 ^ (200 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 200) := by rfl

theorem twelve_packed_row_201 :
    twelvePackedRows 201 = packedMinorResidueRow twelveMinor 2 1024 201 := by rfl

theorem twelve_packed_product_201 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 201) twelvePackedRows =
      1024 ^ (201 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 201) := by rfl

theorem twelve_packed_row_202 :
    twelvePackedRows 202 = packedMinorResidueRow twelveMinor 2 1024 202 := by rfl

theorem twelve_packed_product_202 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 202) twelvePackedRows =
      1024 ^ (202 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 202) := by rfl

theorem twelve_packed_row_203 :
    twelvePackedRows 203 = packedMinorResidueRow twelveMinor 2 1024 203 := by rfl

theorem twelve_packed_product_203 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 203) twelvePackedRows =
      1024 ^ (203 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 203) := by rfl

theorem twelve_packed_row_204 :
    twelvePackedRows 204 = packedMinorResidueRow twelveMinor 2 1024 204 := by rfl

theorem twelve_packed_product_204 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 204) twelvePackedRows =
      1024 ^ (204 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 204) := by rfl

theorem twelve_packed_row_205 :
    twelvePackedRows 205 = packedMinorResidueRow twelveMinor 2 1024 205 := by rfl

theorem twelve_packed_product_205 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 205) twelvePackedRows =
      1024 ^ (205 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 205) := by rfl

theorem twelve_packed_row_206 :
    twelvePackedRows 206 = packedMinorResidueRow twelveMinor 2 1024 206 := by rfl

theorem twelve_packed_product_206 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 206) twelvePackedRows =
      1024 ^ (206 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 206) := by rfl

theorem twelve_packed_row_207 :
    twelvePackedRows 207 = packedMinorResidueRow twelveMinor 2 1024 207 := by rfl

theorem twelve_packed_product_207 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 207) twelvePackedRows =
      1024 ^ (207 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 207) := by rfl

theorem twelve_packed_row_208 :
    twelvePackedRows 208 = packedMinorResidueRow twelveMinor 2 1024 208 := by rfl

theorem twelve_packed_product_208 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 208) twelvePackedRows =
      1024 ^ (208 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 208) := by rfl

theorem twelve_packed_row_209 :
    twelvePackedRows 209 = packedMinorResidueRow twelveMinor 2 1024 209 := by rfl

theorem twelve_packed_product_209 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 209) twelvePackedRows =
      1024 ^ (209 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 209) := by rfl

theorem twelve_packed_row_210 :
    twelvePackedRows 210 = packedMinorResidueRow twelveMinor 2 1024 210 := by rfl

theorem twelve_packed_product_210 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 210) twelvePackedRows =
      1024 ^ (210 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 210) := by rfl

theorem twelve_packed_row_211 :
    twelvePackedRows 211 = packedMinorResidueRow twelveMinor 2 1024 211 := by rfl

theorem twelve_packed_product_211 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 211) twelvePackedRows =
      1024 ^ (211 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 211) := by rfl

theorem twelve_packed_row_212 :
    twelvePackedRows 212 = packedMinorResidueRow twelveMinor 2 1024 212 := by rfl

theorem twelve_packed_product_212 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 212) twelvePackedRows =
      1024 ^ (212 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 212) := by rfl

theorem twelve_packed_row_213 :
    twelvePackedRows 213 = packedMinorResidueRow twelveMinor 2 1024 213 := by rfl

theorem twelve_packed_product_213 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 213) twelvePackedRows =
      1024 ^ (213 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 213) := by rfl

theorem twelve_packed_row_214 :
    twelvePackedRows 214 = packedMinorResidueRow twelveMinor 2 1024 214 := by rfl

theorem twelve_packed_product_214 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 214) twelvePackedRows =
      1024 ^ (214 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 214) := by rfl

theorem twelve_packed_row_215 :
    twelvePackedRows 215 = packedMinorResidueRow twelveMinor 2 1024 215 := by rfl

theorem twelve_packed_product_215 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 215) twelvePackedRows =
      1024 ^ (215 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 215) := by rfl

theorem twelve_packed_row_216 :
    twelvePackedRows 216 = packedMinorResidueRow twelveMinor 2 1024 216 := by rfl

theorem twelve_packed_product_216 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 216) twelvePackedRows =
      1024 ^ (216 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 216) := by rfl

theorem twelve_packed_row_217 :
    twelvePackedRows 217 = packedMinorResidueRow twelveMinor 2 1024 217 := by rfl

theorem twelve_packed_product_217 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 217) twelvePackedRows =
      1024 ^ (217 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 217) := by rfl

theorem twelve_packed_row_218 :
    twelvePackedRows 218 = packedMinorResidueRow twelveMinor 2 1024 218 := by rfl

theorem twelve_packed_product_218 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 218) twelvePackedRows =
      1024 ^ (218 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 218) := by rfl

theorem twelve_packed_row_219 :
    twelvePackedRows 219 = packedMinorResidueRow twelveMinor 2 1024 219 := by rfl

theorem twelve_packed_product_219 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 219) twelvePackedRows =
      1024 ^ (219 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 219) := by rfl

theorem twelve_packed_row_220 :
    twelvePackedRows 220 = packedMinorResidueRow twelveMinor 2 1024 220 := by rfl

theorem twelve_packed_product_220 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 220) twelvePackedRows =
      1024 ^ (220 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 220) := by rfl

theorem twelve_packed_row_221 :
    twelvePackedRows 221 = packedMinorResidueRow twelveMinor 2 1024 221 := by rfl

theorem twelve_packed_product_221 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 221) twelvePackedRows =
      1024 ^ (221 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 221) := by rfl

theorem twelve_packed_row_222 :
    twelvePackedRows 222 = packedMinorResidueRow twelveMinor 2 1024 222 := by rfl

theorem twelve_packed_product_222 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 222) twelvePackedRows =
      1024 ^ (222 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 222) := by rfl

theorem twelve_packed_row_223 :
    twelvePackedRows 223 = packedMinorResidueRow twelveMinor 2 1024 223 := by rfl

theorem twelve_packed_product_223 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 223) twelvePackedRows =
      1024 ^ (223 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 223) := by rfl

theorem twelve_packed_row_224 :
    twelvePackedRows 224 = packedMinorResidueRow twelveMinor 2 1024 224 := by rfl

theorem twelve_packed_product_224 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 224) twelvePackedRows =
      1024 ^ (224 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 224) := by rfl

theorem twelve_packed_row_225 :
    twelvePackedRows 225 = packedMinorResidueRow twelveMinor 2 1024 225 := by rfl

theorem twelve_packed_product_225 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 225) twelvePackedRows =
      1024 ^ (225 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 225) := by rfl

theorem twelve_packed_row_226 :
    twelvePackedRows 226 = packedMinorResidueRow twelveMinor 2 1024 226 := by rfl

theorem twelve_packed_product_226 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 226) twelvePackedRows =
      1024 ^ (226 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 226) := by rfl

theorem twelve_packed_row_227 :
    twelvePackedRows 227 = packedMinorResidueRow twelveMinor 2 1024 227 := by rfl

theorem twelve_packed_product_227 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 227) twelvePackedRows =
      1024 ^ (227 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 227) := by rfl

theorem twelve_packed_row_228 :
    twelvePackedRows 228 = packedMinorResidueRow twelveMinor 2 1024 228 := by rfl

theorem twelve_packed_product_228 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 228) twelvePackedRows =
      1024 ^ (228 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 228) := by rfl

theorem twelve_packed_row_229 :
    twelvePackedRows 229 = packedMinorResidueRow twelveMinor 2 1024 229 := by rfl

theorem twelve_packed_product_229 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 229) twelvePackedRows =
      1024 ^ (229 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 229) := by rfl

theorem twelve_packed_row_230 :
    twelvePackedRows 230 = packedMinorResidueRow twelveMinor 2 1024 230 := by rfl

theorem twelve_packed_product_230 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 230) twelvePackedRows =
      1024 ^ (230 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 230) := by rfl

theorem twelve_packed_row_231 :
    twelvePackedRows 231 = packedMinorResidueRow twelveMinor 2 1024 231 := by rfl

theorem twelve_packed_product_231 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 231) twelvePackedRows =
      1024 ^ (231 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 231) := by rfl

theorem twelve_packed_row_232 :
    twelvePackedRows 232 = packedMinorResidueRow twelveMinor 2 1024 232 := by rfl

theorem twelve_packed_product_232 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 232) twelvePackedRows =
      1024 ^ (232 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 232) := by rfl

theorem twelve_packed_row_233 :
    twelvePackedRows 233 = packedMinorResidueRow twelveMinor 2 1024 233 := by rfl

theorem twelve_packed_product_233 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 233) twelvePackedRows =
      1024 ^ (233 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 233) := by rfl

theorem twelve_packed_row_234 :
    twelvePackedRows 234 = packedMinorResidueRow twelveMinor 2 1024 234 := by rfl

theorem twelve_packed_product_234 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 234) twelvePackedRows =
      1024 ^ (234 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 234) := by rfl

theorem twelve_packed_row_235 :
    twelvePackedRows 235 = packedMinorResidueRow twelveMinor 2 1024 235 := by rfl

theorem twelve_packed_product_235 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 235) twelvePackedRows =
      1024 ^ (235 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 235) := by rfl

theorem twelve_packed_row_236 :
    twelvePackedRows 236 = packedMinorResidueRow twelveMinor 2 1024 236 := by rfl

theorem twelve_packed_product_236 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 236) twelvePackedRows =
      1024 ^ (236 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 236) := by rfl

theorem twelve_packed_row_237 :
    twelvePackedRows 237 = packedMinorResidueRow twelveMinor 2 1024 237 := by rfl

theorem twelve_packed_product_237 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 237) twelvePackedRows =
      1024 ^ (237 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 237) := by rfl

theorem twelve_packed_row_238 :
    twelvePackedRows 238 = packedMinorResidueRow twelveMinor 2 1024 238 := by rfl

theorem twelve_packed_product_238 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 238) twelvePackedRows =
      1024 ^ (238 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 238) := by rfl

theorem twelve_packed_row_239 :
    twelvePackedRows 239 = packedMinorResidueRow twelveMinor 2 1024 239 := by rfl

theorem twelve_packed_product_239 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 239) twelvePackedRows =
      1024 ^ (239 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 239) := by rfl

theorem twelve_packed_row_240 :
    twelvePackedRows 240 = packedMinorResidueRow twelveMinor 2 1024 240 := by rfl

theorem twelve_packed_product_240 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 240) twelvePackedRows =
      1024 ^ (240 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 240) := by rfl

theorem twelve_packed_row_241 :
    twelvePackedRows 241 = packedMinorResidueRow twelveMinor 2 1024 241 := by rfl

theorem twelve_packed_product_241 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 241) twelvePackedRows =
      1024 ^ (241 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 241) := by rfl

theorem twelve_packed_row_242 :
    twelvePackedRows 242 = packedMinorResidueRow twelveMinor 2 1024 242 := by rfl

theorem twelve_packed_product_242 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 242) twelvePackedRows =
      1024 ^ (242 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 242) := by rfl

theorem twelve_packed_row_243 :
    twelvePackedRows 243 = packedMinorResidueRow twelveMinor 2 1024 243 := by rfl

theorem twelve_packed_product_243 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 243) twelvePackedRows =
      1024 ^ (243 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 243) := by rfl

theorem twelve_packed_row_244 :
    twelvePackedRows 244 = packedMinorResidueRow twelveMinor 2 1024 244 := by rfl

theorem twelve_packed_product_244 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 244) twelvePackedRows =
      1024 ^ (244 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 244) := by rfl

theorem twelve_packed_row_245 :
    twelvePackedRows 245 = packedMinorResidueRow twelveMinor 2 1024 245 := by rfl

theorem twelve_packed_product_245 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 245) twelvePackedRows =
      1024 ^ (245 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 245) := by rfl

theorem twelve_packed_row_246 :
    twelvePackedRows 246 = packedMinorResidueRow twelveMinor 2 1024 246 := by rfl

theorem twelve_packed_product_246 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 246) twelvePackedRows =
      1024 ^ (246 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 246) := by rfl

theorem twelve_packed_row_247 :
    twelvePackedRows 247 = packedMinorResidueRow twelveMinor 2 1024 247 := by rfl

theorem twelve_packed_product_247 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 247) twelvePackedRows =
      1024 ^ (247 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 247) := by rfl

theorem twelve_packed_row_248 :
    twelvePackedRows 248 = packedMinorResidueRow twelveMinor 2 1024 248 := by rfl

theorem twelve_packed_product_248 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 248) twelvePackedRows =
      1024 ^ (248 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 248) := by rfl

theorem twelve_packed_row_249 :
    twelvePackedRows 249 = packedMinorResidueRow twelveMinor 2 1024 249 := by rfl

theorem twelve_packed_product_249 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 249) twelvePackedRows =
      1024 ^ (249 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 249) := by rfl

theorem twelve_packed_row_250 :
    twelvePackedRows 250 = packedMinorResidueRow twelveMinor 2 1024 250 := by rfl

theorem twelve_packed_product_250 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 250) twelvePackedRows =
      1024 ^ (250 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 250) := by rfl

theorem twelve_packed_row_251 :
    twelvePackedRows 251 = packedMinorResidueRow twelveMinor 2 1024 251 := by rfl

theorem twelve_packed_product_251 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 251) twelvePackedRows =
      1024 ^ (251 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 251) := by rfl

theorem twelve_packed_row_252 :
    twelvePackedRows 252 = packedMinorResidueRow twelveMinor 2 1024 252 := by rfl

theorem twelve_packed_product_252 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 252) twelvePackedRows =
      1024 ^ (252 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 252) := by rfl

theorem twelve_packed_row_253 :
    twelvePackedRows 253 = packedMinorResidueRow twelveMinor 2 1024 253 := by rfl

theorem twelve_packed_product_253 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 253) twelvePackedRows =
      1024 ^ (253 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 253) := by rfl

theorem twelve_packed_row_254 :
    twelvePackedRows 254 = packedMinorResidueRow twelveMinor 2 1024 254 := by rfl

theorem twelve_packed_product_254 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 254) twelvePackedRows =
      1024 ^ (254 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 254) := by rfl

theorem twelve_packed_row_255 :
    twelvePackedRows 255 = packedMinorResidueRow twelveMinor 2 1024 255 := by rfl

theorem twelve_packed_product_255 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 255) twelvePackedRows =
      1024 ^ (255 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 255) := by rfl

theorem twelve_packed_row_256 :
    twelvePackedRows 256 = packedMinorResidueRow twelveMinor 2 1024 256 := by rfl

theorem twelve_packed_product_256 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 256) twelvePackedRows =
      1024 ^ (256 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 256) := by rfl

theorem twelve_packed_row_257 :
    twelvePackedRows 257 = packedMinorResidueRow twelveMinor 2 1024 257 := by rfl

theorem twelve_packed_product_257 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 257) twelvePackedRows =
      1024 ^ (257 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 257) := by rfl

theorem twelve_packed_row_258 :
    twelvePackedRows 258 = packedMinorResidueRow twelveMinor 2 1024 258 := by rfl

theorem twelve_packed_product_258 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 258) twelvePackedRows =
      1024 ^ (258 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 258) := by rfl

theorem twelve_packed_row_259 :
    twelvePackedRows 259 = packedMinorResidueRow twelveMinor 2 1024 259 := by rfl

theorem twelve_packed_product_259 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 259) twelvePackedRows =
      1024 ^ (259 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 259) := by rfl

theorem twelve_packed_row_260 :
    twelvePackedRows 260 = packedMinorResidueRow twelveMinor 2 1024 260 := by rfl

theorem twelve_packed_product_260 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 260) twelvePackedRows =
      1024 ^ (260 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 260) := by rfl

theorem twelve_packed_row_261 :
    twelvePackedRows 261 = packedMinorResidueRow twelveMinor 2 1024 261 := by rfl

theorem twelve_packed_product_261 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 261) twelvePackedRows =
      1024 ^ (261 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 261) := by rfl

theorem twelve_packed_row_262 :
    twelvePackedRows 262 = packedMinorResidueRow twelveMinor 2 1024 262 := by rfl

theorem twelve_packed_product_262 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 262) twelvePackedRows =
      1024 ^ (262 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 262) := by rfl

theorem twelve_packed_row_263 :
    twelvePackedRows 263 = packedMinorResidueRow twelveMinor 2 1024 263 := by rfl

theorem twelve_packed_product_263 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 263) twelvePackedRows =
      1024 ^ (263 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 263) := by rfl

theorem twelve_packed_row_264 :
    twelvePackedRows 264 = packedMinorResidueRow twelveMinor 2 1024 264 := by rfl

theorem twelve_packed_product_264 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 264) twelvePackedRows =
      1024 ^ (264 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 264) := by rfl

theorem twelve_packed_row_265 :
    twelvePackedRows 265 = packedMinorResidueRow twelveMinor 2 1024 265 := by rfl

theorem twelve_packed_product_265 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 265) twelvePackedRows =
      1024 ^ (265 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 265) := by rfl

theorem twelve_packed_row_266 :
    twelvePackedRows 266 = packedMinorResidueRow twelveMinor 2 1024 266 := by rfl

theorem twelve_packed_product_266 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 266) twelvePackedRows =
      1024 ^ (266 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 266) := by rfl

theorem twelve_packed_row_267 :
    twelvePackedRows 267 = packedMinorResidueRow twelveMinor 2 1024 267 := by rfl

theorem twelve_packed_product_267 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 267) twelvePackedRows =
      1024 ^ (267 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 267) := by rfl

theorem twelve_packed_row_268 :
    twelvePackedRows 268 = packedMinorResidueRow twelveMinor 2 1024 268 := by rfl

theorem twelve_packed_product_268 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 268) twelvePackedRows =
      1024 ^ (268 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 268) := by rfl

theorem twelve_packed_row_269 :
    twelvePackedRows 269 = packedMinorResidueRow twelveMinor 2 1024 269 := by rfl

theorem twelve_packed_product_269 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 269) twelvePackedRows =
      1024 ^ (269 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 269) := by rfl

theorem twelve_packed_row_270 :
    twelvePackedRows 270 = packedMinorResidueRow twelveMinor 2 1024 270 := by rfl

theorem twelve_packed_product_270 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 270) twelvePackedRows =
      1024 ^ (270 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 270) := by rfl

theorem twelve_packed_row_271 :
    twelvePackedRows 271 = packedMinorResidueRow twelveMinor 2 1024 271 := by rfl

theorem twelve_packed_product_271 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 271) twelvePackedRows =
      1024 ^ (271 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 271) := by rfl

theorem twelve_packed_row_272 :
    twelvePackedRows 272 = packedMinorResidueRow twelveMinor 2 1024 272 := by rfl

theorem twelve_packed_product_272 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 272) twelvePackedRows =
      1024 ^ (272 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 272) := by rfl

theorem twelve_packed_row_273 :
    twelvePackedRows 273 = packedMinorResidueRow twelveMinor 2 1024 273 := by rfl

theorem twelve_packed_product_273 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 273) twelvePackedRows =
      1024 ^ (273 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 273) := by rfl

theorem twelve_packed_row_274 :
    twelvePackedRows 274 = packedMinorResidueRow twelveMinor 2 1024 274 := by rfl

theorem twelve_packed_product_274 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 274) twelvePackedRows =
      1024 ^ (274 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 274) := by rfl

theorem twelve_packed_row_275 :
    twelvePackedRows 275 = packedMinorResidueRow twelveMinor 2 1024 275 := by rfl

theorem twelve_packed_product_275 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 275) twelvePackedRows =
      1024 ^ (275 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 275) := by rfl

theorem twelve_packed_row_276 :
    twelvePackedRows 276 = packedMinorResidueRow twelveMinor 2 1024 276 := by rfl

theorem twelve_packed_product_276 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 276) twelvePackedRows =
      1024 ^ (276 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 276) := by rfl

theorem twelve_packed_row_277 :
    twelvePackedRows 277 = packedMinorResidueRow twelveMinor 2 1024 277 := by rfl

theorem twelve_packed_product_277 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 277) twelvePackedRows =
      1024 ^ (277 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 277) := by rfl

theorem twelve_packed_row_278 :
    twelvePackedRows 278 = packedMinorResidueRow twelveMinor 2 1024 278 := by rfl

theorem twelve_packed_product_278 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 278) twelvePackedRows =
      1024 ^ (278 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 278) := by rfl

theorem twelve_packed_row_279 :
    twelvePackedRows 279 = packedMinorResidueRow twelveMinor 2 1024 279 := by rfl

theorem twelve_packed_product_279 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 279) twelvePackedRows =
      1024 ^ (279 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 279) := by rfl

theorem twelve_packed_row_280 :
    twelvePackedRows 280 = packedMinorResidueRow twelveMinor 2 1024 280 := by rfl

theorem twelve_packed_product_280 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 280) twelvePackedRows =
      1024 ^ (280 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 280) := by rfl

theorem twelve_packed_row_281 :
    twelvePackedRows 281 = packedMinorResidueRow twelveMinor 2 1024 281 := by rfl

theorem twelve_packed_product_281 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 281) twelvePackedRows =
      1024 ^ (281 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 281) := by rfl

theorem twelve_packed_row_282 :
    twelvePackedRows 282 = packedMinorResidueRow twelveMinor 2 1024 282 := by rfl

theorem twelve_packed_product_282 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 282) twelvePackedRows =
      1024 ^ (282 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 282) := by rfl

theorem twelve_packed_row_283 :
    twelvePackedRows 283 = packedMinorResidueRow twelveMinor 2 1024 283 := by rfl

theorem twelve_packed_product_283 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 283) twelvePackedRows =
      1024 ^ (283 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 283) := by rfl

theorem twelve_packed_row_284 :
    twelvePackedRows 284 = packedMinorResidueRow twelveMinor 2 1024 284 := by rfl

theorem twelve_packed_product_284 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 284) twelvePackedRows =
      1024 ^ (284 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 284) := by rfl

theorem twelve_packed_row_285 :
    twelvePackedRows 285 = packedMinorResidueRow twelveMinor 2 1024 285 := by rfl

theorem twelve_packed_product_285 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 285) twelvePackedRows =
      1024 ^ (285 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 285) := by rfl

theorem twelve_packed_row_286 :
    twelvePackedRows 286 = packedMinorResidueRow twelveMinor 2 1024 286 := by rfl

theorem twelve_packed_product_286 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 286) twelvePackedRows =
      1024 ^ (286 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 286) := by rfl

theorem twelve_packed_row_287 :
    twelvePackedRows 287 = packedMinorResidueRow twelveMinor 2 1024 287 := by rfl

theorem twelve_packed_product_287 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 287) twelvePackedRows =
      1024 ^ (287 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 287) := by rfl

end IdealGeneration.QuadraticLowDimension
