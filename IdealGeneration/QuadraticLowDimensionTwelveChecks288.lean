module

public import IdealGeneration.QuadraticLowDimensionTwelveData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact arithmetic checks for rows 288–383 of the twelve-variable certificate. -/

noncomputable section
namespace IdealGeneration.QuadraticLowDimension
open CertifiedRank
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024


theorem twelve_packed_row_288 :
    twelvePackedRows 288 = packedMinorResidueRow twelveMinor 2 1024 288 := by rfl

theorem twelve_packed_product_288 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 288) twelvePackedRows =
      1024 ^ (288 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 288) := by rfl

theorem twelve_packed_row_289 :
    twelvePackedRows 289 = packedMinorResidueRow twelveMinor 2 1024 289 := by rfl

theorem twelve_packed_product_289 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 289) twelvePackedRows =
      1024 ^ (289 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 289) := by rfl

theorem twelve_packed_row_290 :
    twelvePackedRows 290 = packedMinorResidueRow twelveMinor 2 1024 290 := by rfl

theorem twelve_packed_product_290 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 290) twelvePackedRows =
      1024 ^ (290 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 290) := by rfl

theorem twelve_packed_row_291 :
    twelvePackedRows 291 = packedMinorResidueRow twelveMinor 2 1024 291 := by rfl

theorem twelve_packed_product_291 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 291) twelvePackedRows =
      1024 ^ (291 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 291) := by rfl

theorem twelve_packed_row_292 :
    twelvePackedRows 292 = packedMinorResidueRow twelveMinor 2 1024 292 := by rfl

theorem twelve_packed_product_292 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 292) twelvePackedRows =
      1024 ^ (292 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 292) := by rfl

theorem twelve_packed_row_293 :
    twelvePackedRows 293 = packedMinorResidueRow twelveMinor 2 1024 293 := by rfl

theorem twelve_packed_product_293 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 293) twelvePackedRows =
      1024 ^ (293 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 293) := by rfl

theorem twelve_packed_row_294 :
    twelvePackedRows 294 = packedMinorResidueRow twelveMinor 2 1024 294 := by rfl

theorem twelve_packed_product_294 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 294) twelvePackedRows =
      1024 ^ (294 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 294) := by rfl

theorem twelve_packed_row_295 :
    twelvePackedRows 295 = packedMinorResidueRow twelveMinor 2 1024 295 := by rfl

theorem twelve_packed_product_295 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 295) twelvePackedRows =
      1024 ^ (295 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 295) := by rfl

theorem twelve_packed_row_296 :
    twelvePackedRows 296 = packedMinorResidueRow twelveMinor 2 1024 296 := by rfl

theorem twelve_packed_product_296 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 296) twelvePackedRows =
      1024 ^ (296 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 296) := by rfl

theorem twelve_packed_row_297 :
    twelvePackedRows 297 = packedMinorResidueRow twelveMinor 2 1024 297 := by rfl

theorem twelve_packed_product_297 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 297) twelvePackedRows =
      1024 ^ (297 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 297) := by rfl

theorem twelve_packed_row_298 :
    twelvePackedRows 298 = packedMinorResidueRow twelveMinor 2 1024 298 := by rfl

theorem twelve_packed_product_298 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 298) twelvePackedRows =
      1024 ^ (298 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 298) := by rfl

theorem twelve_packed_row_299 :
    twelvePackedRows 299 = packedMinorResidueRow twelveMinor 2 1024 299 := by rfl

theorem twelve_packed_product_299 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 299) twelvePackedRows =
      1024 ^ (299 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 299) := by rfl

theorem twelve_packed_row_300 :
    twelvePackedRows 300 = packedMinorResidueRow twelveMinor 2 1024 300 := by rfl

theorem twelve_packed_product_300 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 300) twelvePackedRows =
      1024 ^ (300 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 300) := by rfl

theorem twelve_packed_row_301 :
    twelvePackedRows 301 = packedMinorResidueRow twelveMinor 2 1024 301 := by rfl

theorem twelve_packed_product_301 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 301) twelvePackedRows =
      1024 ^ (301 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 301) := by rfl

theorem twelve_packed_row_302 :
    twelvePackedRows 302 = packedMinorResidueRow twelveMinor 2 1024 302 := by rfl

theorem twelve_packed_product_302 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 302) twelvePackedRows =
      1024 ^ (302 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 302) := by rfl

theorem twelve_packed_row_303 :
    twelvePackedRows 303 = packedMinorResidueRow twelveMinor 2 1024 303 := by rfl

theorem twelve_packed_product_303 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 303) twelvePackedRows =
      1024 ^ (303 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 303) := by rfl

theorem twelve_packed_row_304 :
    twelvePackedRows 304 = packedMinorResidueRow twelveMinor 2 1024 304 := by rfl

theorem twelve_packed_product_304 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 304) twelvePackedRows =
      1024 ^ (304 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 304) := by rfl

theorem twelve_packed_row_305 :
    twelvePackedRows 305 = packedMinorResidueRow twelveMinor 2 1024 305 := by rfl

theorem twelve_packed_product_305 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 305) twelvePackedRows =
      1024 ^ (305 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 305) := by rfl

theorem twelve_packed_row_306 :
    twelvePackedRows 306 = packedMinorResidueRow twelveMinor 2 1024 306 := by rfl

theorem twelve_packed_product_306 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 306) twelvePackedRows =
      1024 ^ (306 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 306) := by rfl

theorem twelve_packed_row_307 :
    twelvePackedRows 307 = packedMinorResidueRow twelveMinor 2 1024 307 := by rfl

theorem twelve_packed_product_307 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 307) twelvePackedRows =
      1024 ^ (307 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 307) := by rfl

theorem twelve_packed_row_308 :
    twelvePackedRows 308 = packedMinorResidueRow twelveMinor 2 1024 308 := by rfl

theorem twelve_packed_product_308 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 308) twelvePackedRows =
      1024 ^ (308 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 308) := by rfl

theorem twelve_packed_row_309 :
    twelvePackedRows 309 = packedMinorResidueRow twelveMinor 2 1024 309 := by rfl

theorem twelve_packed_product_309 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 309) twelvePackedRows =
      1024 ^ (309 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 309) := by rfl

theorem twelve_packed_row_310 :
    twelvePackedRows 310 = packedMinorResidueRow twelveMinor 2 1024 310 := by rfl

theorem twelve_packed_product_310 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 310) twelvePackedRows =
      1024 ^ (310 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 310) := by rfl

theorem twelve_packed_row_311 :
    twelvePackedRows 311 = packedMinorResidueRow twelveMinor 2 1024 311 := by rfl

theorem twelve_packed_product_311 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 311) twelvePackedRows =
      1024 ^ (311 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 311) := by rfl

theorem twelve_packed_row_312 :
    twelvePackedRows 312 = packedMinorResidueRow twelveMinor 2 1024 312 := by rfl

theorem twelve_packed_product_312 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 312) twelvePackedRows =
      1024 ^ (312 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 312) := by rfl

theorem twelve_packed_row_313 :
    twelvePackedRows 313 = packedMinorResidueRow twelveMinor 2 1024 313 := by rfl

theorem twelve_packed_product_313 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 313) twelvePackedRows =
      1024 ^ (313 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 313) := by rfl

theorem twelve_packed_row_314 :
    twelvePackedRows 314 = packedMinorResidueRow twelveMinor 2 1024 314 := by rfl

theorem twelve_packed_product_314 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 314) twelvePackedRows =
      1024 ^ (314 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 314) := by rfl

theorem twelve_packed_row_315 :
    twelvePackedRows 315 = packedMinorResidueRow twelveMinor 2 1024 315 := by rfl

theorem twelve_packed_product_315 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 315) twelvePackedRows =
      1024 ^ (315 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 315) := by rfl

theorem twelve_packed_row_316 :
    twelvePackedRows 316 = packedMinorResidueRow twelveMinor 2 1024 316 := by rfl

theorem twelve_packed_product_316 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 316) twelvePackedRows =
      1024 ^ (316 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 316) := by rfl

theorem twelve_packed_row_317 :
    twelvePackedRows 317 = packedMinorResidueRow twelveMinor 2 1024 317 := by rfl

theorem twelve_packed_product_317 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 317) twelvePackedRows =
      1024 ^ (317 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 317) := by rfl

theorem twelve_packed_row_318 :
    twelvePackedRows 318 = packedMinorResidueRow twelveMinor 2 1024 318 := by rfl

theorem twelve_packed_product_318 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 318) twelvePackedRows =
      1024 ^ (318 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 318) := by rfl

theorem twelve_packed_row_319 :
    twelvePackedRows 319 = packedMinorResidueRow twelveMinor 2 1024 319 := by rfl

theorem twelve_packed_product_319 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 319) twelvePackedRows =
      1024 ^ (319 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 319) := by rfl

theorem twelve_packed_row_320 :
    twelvePackedRows 320 = packedMinorResidueRow twelveMinor 2 1024 320 := by rfl

theorem twelve_packed_product_320 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 320) twelvePackedRows =
      1024 ^ (320 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 320) := by rfl

theorem twelve_packed_row_321 :
    twelvePackedRows 321 = packedMinorResidueRow twelveMinor 2 1024 321 := by rfl

theorem twelve_packed_product_321 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 321) twelvePackedRows =
      1024 ^ (321 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 321) := by rfl

theorem twelve_packed_row_322 :
    twelvePackedRows 322 = packedMinorResidueRow twelveMinor 2 1024 322 := by rfl

theorem twelve_packed_product_322 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 322) twelvePackedRows =
      1024 ^ (322 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 322) := by rfl

theorem twelve_packed_row_323 :
    twelvePackedRows 323 = packedMinorResidueRow twelveMinor 2 1024 323 := by rfl

theorem twelve_packed_product_323 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 323) twelvePackedRows =
      1024 ^ (323 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 323) := by rfl

theorem twelve_packed_row_324 :
    twelvePackedRows 324 = packedMinorResidueRow twelveMinor 2 1024 324 := by rfl

theorem twelve_packed_product_324 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 324) twelvePackedRows =
      1024 ^ (324 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 324) := by rfl

theorem twelve_packed_row_325 :
    twelvePackedRows 325 = packedMinorResidueRow twelveMinor 2 1024 325 := by rfl

theorem twelve_packed_product_325 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 325) twelvePackedRows =
      1024 ^ (325 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 325) := by rfl

theorem twelve_packed_row_326 :
    twelvePackedRows 326 = packedMinorResidueRow twelveMinor 2 1024 326 := by rfl

theorem twelve_packed_product_326 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 326) twelvePackedRows =
      1024 ^ (326 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 326) := by rfl

theorem twelve_packed_row_327 :
    twelvePackedRows 327 = packedMinorResidueRow twelveMinor 2 1024 327 := by rfl

theorem twelve_packed_product_327 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 327) twelvePackedRows =
      1024 ^ (327 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 327) := by rfl

theorem twelve_packed_row_328 :
    twelvePackedRows 328 = packedMinorResidueRow twelveMinor 2 1024 328 := by rfl

theorem twelve_packed_product_328 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 328) twelvePackedRows =
      1024 ^ (328 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 328) := by rfl

theorem twelve_packed_row_329 :
    twelvePackedRows 329 = packedMinorResidueRow twelveMinor 2 1024 329 := by rfl

theorem twelve_packed_product_329 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 329) twelvePackedRows =
      1024 ^ (329 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 329) := by rfl

theorem twelve_packed_row_330 :
    twelvePackedRows 330 = packedMinorResidueRow twelveMinor 2 1024 330 := by rfl

theorem twelve_packed_product_330 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 330) twelvePackedRows =
      1024 ^ (330 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 330) := by rfl

theorem twelve_packed_row_331 :
    twelvePackedRows 331 = packedMinorResidueRow twelveMinor 2 1024 331 := by rfl

theorem twelve_packed_product_331 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 331) twelvePackedRows =
      1024 ^ (331 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 331) := by rfl

theorem twelve_packed_row_332 :
    twelvePackedRows 332 = packedMinorResidueRow twelveMinor 2 1024 332 := by rfl

theorem twelve_packed_product_332 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 332) twelvePackedRows =
      1024 ^ (332 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 332) := by rfl

theorem twelve_packed_row_333 :
    twelvePackedRows 333 = packedMinorResidueRow twelveMinor 2 1024 333 := by rfl

theorem twelve_packed_product_333 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 333) twelvePackedRows =
      1024 ^ (333 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 333) := by rfl

theorem twelve_packed_row_334 :
    twelvePackedRows 334 = packedMinorResidueRow twelveMinor 2 1024 334 := by rfl

theorem twelve_packed_product_334 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 334) twelvePackedRows =
      1024 ^ (334 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 334) := by rfl

theorem twelve_packed_row_335 :
    twelvePackedRows 335 = packedMinorResidueRow twelveMinor 2 1024 335 := by rfl

theorem twelve_packed_product_335 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 335) twelvePackedRows =
      1024 ^ (335 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 335) := by rfl

theorem twelve_packed_row_336 :
    twelvePackedRows 336 = packedMinorResidueRow twelveMinor 2 1024 336 := by rfl

theorem twelve_packed_product_336 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 336) twelvePackedRows =
      1024 ^ (336 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 336) := by rfl

theorem twelve_packed_row_337 :
    twelvePackedRows 337 = packedMinorResidueRow twelveMinor 2 1024 337 := by rfl

theorem twelve_packed_product_337 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 337) twelvePackedRows =
      1024 ^ (337 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 337) := by rfl

theorem twelve_packed_row_338 :
    twelvePackedRows 338 = packedMinorResidueRow twelveMinor 2 1024 338 := by rfl

theorem twelve_packed_product_338 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 338) twelvePackedRows =
      1024 ^ (338 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 338) := by rfl

theorem twelve_packed_row_339 :
    twelvePackedRows 339 = packedMinorResidueRow twelveMinor 2 1024 339 := by rfl

theorem twelve_packed_product_339 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 339) twelvePackedRows =
      1024 ^ (339 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 339) := by rfl

theorem twelve_packed_row_340 :
    twelvePackedRows 340 = packedMinorResidueRow twelveMinor 2 1024 340 := by rfl

theorem twelve_packed_product_340 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 340) twelvePackedRows =
      1024 ^ (340 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 340) := by rfl

theorem twelve_packed_row_341 :
    twelvePackedRows 341 = packedMinorResidueRow twelveMinor 2 1024 341 := by rfl

theorem twelve_packed_product_341 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 341) twelvePackedRows =
      1024 ^ (341 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 341) := by rfl

theorem twelve_packed_row_342 :
    twelvePackedRows 342 = packedMinorResidueRow twelveMinor 2 1024 342 := by rfl

theorem twelve_packed_product_342 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 342) twelvePackedRows =
      1024 ^ (342 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 342) := by rfl

theorem twelve_packed_row_343 :
    twelvePackedRows 343 = packedMinorResidueRow twelveMinor 2 1024 343 := by rfl

theorem twelve_packed_product_343 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 343) twelvePackedRows =
      1024 ^ (343 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 343) := by rfl

theorem twelve_packed_row_344 :
    twelvePackedRows 344 = packedMinorResidueRow twelveMinor 2 1024 344 := by rfl

theorem twelve_packed_product_344 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 344) twelvePackedRows =
      1024 ^ (344 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 344) := by rfl

theorem twelve_packed_row_345 :
    twelvePackedRows 345 = packedMinorResidueRow twelveMinor 2 1024 345 := by rfl

theorem twelve_packed_product_345 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 345) twelvePackedRows =
      1024 ^ (345 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 345) := by rfl

theorem twelve_packed_row_346 :
    twelvePackedRows 346 = packedMinorResidueRow twelveMinor 2 1024 346 := by rfl

theorem twelve_packed_product_346 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 346) twelvePackedRows =
      1024 ^ (346 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 346) := by rfl

theorem twelve_packed_row_347 :
    twelvePackedRows 347 = packedMinorResidueRow twelveMinor 2 1024 347 := by rfl

theorem twelve_packed_product_347 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 347) twelvePackedRows =
      1024 ^ (347 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 347) := by rfl

theorem twelve_packed_row_348 :
    twelvePackedRows 348 = packedMinorResidueRow twelveMinor 2 1024 348 := by rfl

theorem twelve_packed_product_348 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 348) twelvePackedRows =
      1024 ^ (348 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 348) := by rfl

theorem twelve_packed_row_349 :
    twelvePackedRows 349 = packedMinorResidueRow twelveMinor 2 1024 349 := by rfl

theorem twelve_packed_product_349 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 349) twelvePackedRows =
      1024 ^ (349 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 349) := by rfl

theorem twelve_packed_row_350 :
    twelvePackedRows 350 = packedMinorResidueRow twelveMinor 2 1024 350 := by rfl

theorem twelve_packed_product_350 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 350) twelvePackedRows =
      1024 ^ (350 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 350) := by rfl

theorem twelve_packed_row_351 :
    twelvePackedRows 351 = packedMinorResidueRow twelveMinor 2 1024 351 := by rfl

theorem twelve_packed_product_351 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 351) twelvePackedRows =
      1024 ^ (351 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 351) := by rfl

theorem twelve_packed_row_352 :
    twelvePackedRows 352 = packedMinorResidueRow twelveMinor 2 1024 352 := by rfl

theorem twelve_packed_product_352 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 352) twelvePackedRows =
      1024 ^ (352 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 352) := by rfl

theorem twelve_packed_row_353 :
    twelvePackedRows 353 = packedMinorResidueRow twelveMinor 2 1024 353 := by rfl

theorem twelve_packed_product_353 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 353) twelvePackedRows =
      1024 ^ (353 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 353) := by rfl

theorem twelve_packed_row_354 :
    twelvePackedRows 354 = packedMinorResidueRow twelveMinor 2 1024 354 := by rfl

theorem twelve_packed_product_354 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 354) twelvePackedRows =
      1024 ^ (354 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 354) := by rfl

theorem twelve_packed_row_355 :
    twelvePackedRows 355 = packedMinorResidueRow twelveMinor 2 1024 355 := by rfl

theorem twelve_packed_product_355 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 355) twelvePackedRows =
      1024 ^ (355 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 355) := by rfl

theorem twelve_packed_row_356 :
    twelvePackedRows 356 = packedMinorResidueRow twelveMinor 2 1024 356 := by rfl

theorem twelve_packed_product_356 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 356) twelvePackedRows =
      1024 ^ (356 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 356) := by rfl

theorem twelve_packed_row_357 :
    twelvePackedRows 357 = packedMinorResidueRow twelveMinor 2 1024 357 := by rfl

theorem twelve_packed_product_357 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 357) twelvePackedRows =
      1024 ^ (357 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 357) := by rfl

theorem twelve_packed_row_358 :
    twelvePackedRows 358 = packedMinorResidueRow twelveMinor 2 1024 358 := by rfl

theorem twelve_packed_product_358 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 358) twelvePackedRows =
      1024 ^ (358 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 358) := by rfl

theorem twelve_packed_row_359 :
    twelvePackedRows 359 = packedMinorResidueRow twelveMinor 2 1024 359 := by rfl

theorem twelve_packed_product_359 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 359) twelvePackedRows =
      1024 ^ (359 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 359) := by rfl

theorem twelve_packed_row_360 :
    twelvePackedRows 360 = packedMinorResidueRow twelveMinor 2 1024 360 := by rfl

theorem twelve_packed_product_360 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 360) twelvePackedRows =
      1024 ^ (360 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 360) := by rfl

theorem twelve_packed_row_361 :
    twelvePackedRows 361 = packedMinorResidueRow twelveMinor 2 1024 361 := by rfl

theorem twelve_packed_product_361 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 361) twelvePackedRows =
      1024 ^ (361 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 361) := by rfl

theorem twelve_packed_row_362 :
    twelvePackedRows 362 = packedMinorResidueRow twelveMinor 2 1024 362 := by rfl

theorem twelve_packed_product_362 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 362) twelvePackedRows =
      1024 ^ (362 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 362) := by rfl

theorem twelve_packed_row_363 :
    twelvePackedRows 363 = packedMinorResidueRow twelveMinor 2 1024 363 := by rfl

theorem twelve_packed_product_363 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 363) twelvePackedRows =
      1024 ^ (363 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 363) := by rfl

theorem twelve_packed_row_364 :
    twelvePackedRows 364 = packedMinorResidueRow twelveMinor 2 1024 364 := by rfl

theorem twelve_packed_product_364 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 364) twelvePackedRows =
      1024 ^ (364 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 364) := by rfl

theorem twelve_packed_row_365 :
    twelvePackedRows 365 = packedMinorResidueRow twelveMinor 2 1024 365 := by rfl

theorem twelve_packed_product_365 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 365) twelvePackedRows =
      1024 ^ (365 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 365) := by rfl

theorem twelve_packed_row_366 :
    twelvePackedRows 366 = packedMinorResidueRow twelveMinor 2 1024 366 := by rfl

theorem twelve_packed_product_366 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 366) twelvePackedRows =
      1024 ^ (366 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 366) := by rfl

theorem twelve_packed_row_367 :
    twelvePackedRows 367 = packedMinorResidueRow twelveMinor 2 1024 367 := by rfl

theorem twelve_packed_product_367 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 367) twelvePackedRows =
      1024 ^ (367 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 367) := by rfl

theorem twelve_packed_row_368 :
    twelvePackedRows 368 = packedMinorResidueRow twelveMinor 2 1024 368 := by rfl

theorem twelve_packed_product_368 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 368) twelvePackedRows =
      1024 ^ (368 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 368) := by rfl

theorem twelve_packed_row_369 :
    twelvePackedRows 369 = packedMinorResidueRow twelveMinor 2 1024 369 := by rfl

theorem twelve_packed_product_369 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 369) twelvePackedRows =
      1024 ^ (369 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 369) := by rfl

theorem twelve_packed_row_370 :
    twelvePackedRows 370 = packedMinorResidueRow twelveMinor 2 1024 370 := by rfl

theorem twelve_packed_product_370 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 370) twelvePackedRows =
      1024 ^ (370 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 370) := by rfl

theorem twelve_packed_row_371 :
    twelvePackedRows 371 = packedMinorResidueRow twelveMinor 2 1024 371 := by rfl

theorem twelve_packed_product_371 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 371) twelvePackedRows =
      1024 ^ (371 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 371) := by rfl

theorem twelve_packed_row_372 :
    twelvePackedRows 372 = packedMinorResidueRow twelveMinor 2 1024 372 := by rfl

theorem twelve_packed_product_372 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 372) twelvePackedRows =
      1024 ^ (372 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 372) := by rfl

theorem twelve_packed_row_373 :
    twelvePackedRows 373 = packedMinorResidueRow twelveMinor 2 1024 373 := by rfl

theorem twelve_packed_product_373 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 373) twelvePackedRows =
      1024 ^ (373 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 373) := by rfl

theorem twelve_packed_row_374 :
    twelvePackedRows 374 = packedMinorResidueRow twelveMinor 2 1024 374 := by rfl

theorem twelve_packed_product_374 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 374) twelvePackedRows =
      1024 ^ (374 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 374) := by rfl

theorem twelve_packed_row_375 :
    twelvePackedRows 375 = packedMinorResidueRow twelveMinor 2 1024 375 := by rfl

theorem twelve_packed_product_375 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 375) twelvePackedRows =
      1024 ^ (375 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 375) := by rfl

theorem twelve_packed_row_376 :
    twelvePackedRows 376 = packedMinorResidueRow twelveMinor 2 1024 376 := by rfl

theorem twelve_packed_product_376 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 376) twelvePackedRows =
      1024 ^ (376 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 376) := by rfl

theorem twelve_packed_row_377 :
    twelvePackedRows 377 = packedMinorResidueRow twelveMinor 2 1024 377 := by rfl

theorem twelve_packed_product_377 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 377) twelvePackedRows =
      1024 ^ (377 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 377) := by rfl

theorem twelve_packed_row_378 :
    twelvePackedRows 378 = packedMinorResidueRow twelveMinor 2 1024 378 := by rfl

theorem twelve_packed_product_378 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 378) twelvePackedRows =
      1024 ^ (378 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 378) := by rfl

theorem twelve_packed_row_379 :
    twelvePackedRows 379 = packedMinorResidueRow twelveMinor 2 1024 379 := by rfl

theorem twelve_packed_product_379 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 379) twelvePackedRows =
      1024 ^ (379 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 379) := by rfl

theorem twelve_packed_row_380 :
    twelvePackedRows 380 = packedMinorResidueRow twelveMinor 2 1024 380 := by rfl

theorem twelve_packed_product_380 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 380) twelvePackedRows =
      1024 ^ (380 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 380) := by rfl

theorem twelve_packed_row_381 :
    twelvePackedRows 381 = packedMinorResidueRow twelveMinor 2 1024 381 := by rfl

theorem twelve_packed_product_381 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 381) twelvePackedRows =
      1024 ^ (381 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 381) := by rfl

theorem twelve_packed_row_382 :
    twelvePackedRows 382 = packedMinorResidueRow twelveMinor 2 1024 382 := by rfl

theorem twelve_packed_product_382 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 382) twelvePackedRows =
      1024 ^ (382 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 382) := by rfl

theorem twelve_packed_row_383 :
    twelvePackedRows 383 = packedMinorResidueRow twelveMinor 2 1024 383 := by rfl

theorem twelve_packed_product_383 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 383) twelvePackedRows =
      1024 ^ (383 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 383) := by rfl

end IdealGeneration.QuadraticLowDimension
