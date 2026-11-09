module

public import IdealGeneration.QuadraticLowDimensionCore
public import IdealGeneration.QuadraticLowDimensionPacked

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact critical quadratic witness in 5 homogeneous variables. -/

noncomputable section
namespace IdealGeneration.QuadraticLowDimension
open CertifiedRank
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

local instance fivePrimeCertificate : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩

private def fivePointDigits (i : Fin 10) : ℕ :=
  if i.val < 5 then
    if i.val < 2 then
      if i.val < 1 then
        8
      else
        11
    else
      if i.val < 3 then
        5
      else
        if i.val < 4 then
          12
        else
          14
  else
    if i.val < 7 then
      if i.val < 6 then
        10
      else
        15
    else
      if i.val < 8 then
        0
      else
        if i.val < 9 then
          7
        else
          6

private def fivePoints : Fin 10 × Fin 4 → ℤ :=
  fun ij => (certificateDigit 2 (fivePointDigits ij.1) ij.2.val : ℤ)

private def fiveRows : Fin 40 → Fin 10 × Fin 4 :=
  (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin (10 * 4)).symm

private def fiveCols (i : Fin 40) : Fin 5 × Fin 5 × Fin 5 :=
  if i.val < 20 then
    if i.val < 10 then
      if i.val < 5 then
        if i.val < 2 then
          if i.val < 1 then
            (0, 1, 0)
          else
            (0, 2, 0)
        else
          if i.val < 3 then
            (0, 3, 0)
          else
            if i.val < 4 then
              (0, 4, 0)
            else
              (1, 0, 1)
      else
        if i.val < 7 then
          if i.val < 6 then
            (1, 2, 1)
          else
            (1, 3, 1)
        else
          if i.val < 8 then
            (1, 4, 1)
          else
            if i.val < 9 then
              (2, 0, 2)
            else
              (2, 1, 2)
    else
      if i.val < 15 then
        if i.val < 12 then
          if i.val < 11 then
            (2, 3, 2)
          else
            (2, 4, 2)
        else
          if i.val < 13 then
            (3, 0, 3)
          else
            if i.val < 14 then
              (3, 1, 3)
            else
              (3, 2, 3)
      else
        if i.val < 17 then
          if i.val < 16 then
            (3, 4, 3)
          else
            (4, 0, 4)
        else
          if i.val < 18 then
            (4, 1, 4)
          else
            if i.val < 19 then
              (4, 2, 4)
            else
              (4, 3, 4)
  else
    if i.val < 30 then
      if i.val < 25 then
        if i.val < 22 then
          if i.val < 21 then
            (0, 1, 2)
          else
            (0, 2, 1)
        else
          if i.val < 23 then
            (0, 1, 3)
          else
            if i.val < 24 then
              (0, 3, 1)
            else
              (0, 1, 4)
      else
        if i.val < 27 then
          if i.val < 26 then
            (0, 4, 1)
          else
            (0, 2, 3)
        else
          if i.val < 28 then
            (0, 3, 2)
          else
            if i.val < 29 then
              (0, 2, 4)
            else
              (0, 4, 2)
    else
      if i.val < 35 then
        if i.val < 32 then
          if i.val < 31 then
            (0, 3, 4)
          else
            (0, 4, 3)
        else
          if i.val < 33 then
            (1, 2, 3)
          else
            if i.val < 34 then
              (1, 3, 2)
            else
              (1, 2, 4)
      else
        if i.val < 37 then
          if i.val < 36 then
            (1, 4, 2)
          else
            (1, 3, 4)
        else
          if i.val < 38 then
            (1, 4, 3)
          else
            if i.val < 39 then
              (2, 3, 4)
            else
              (2, 4, 3)

private def fiveMinor : Matrix (Fin 40) (Fin 40) ℤ :=
  quadraticMinorMatrix fivePoints fiveRows fiveCols

private def fivePackedInverse (i : Fin 40) : ℕ :=
  if i.val < 20 then
    if i.val < 10 then
      if i.val < 5 then
        if i.val < 2 then
          if i.val < 1 then
            365551161729
          else
            17891344
        else
          if i.val < 3 then
            73031286784
          else
            if i.val < 4 then
              292554609041
            else
              163791762987
      else
        if i.val < 7 then
          if i.val < 6 then
            2236418
          else
            155201688619
        else
          if i.val < 8 then
            155199591465
          else
            if i.val < 9 then
              71565376
            else
              4472836
    else
      if i.val < 15 then
        if i.val < 12 then
          if i.val < 11 then
            293168436261
          else
            293168419873
        else
          if i.val < 13 then
            584250294272
          else
            if i.val < 14 then
              541678078081
            else
              1093581899913
      else
        if i.val < 17 then
          if i.val < 16 then
            2147483656
          else
            268435456
        else
          if i.val < 18 then
            536870912
          else
            if i.val < 19 then
              1073741824
            else
              2147483648
  else
    if i.val < 30 then
      if i.val < 25 then
        if i.val < 22 then
          if i.val < 21 then
            35782688
          else
            36900897
        else
          if i.val < 23 then
            146062573568
          else
            if i.val < 24 then
              507318829185
            else
              348900157322
      else
        if i.val < 27 then
          if i.val < 26 then
            150360756513
          else
            292125147136
        else
          if i.val < 28 then
            143130752
          else
            if i.val < 29 then
              292181905521
            else
              263061680
    else
      if i.val < 35 then
        if i.val < 32 then
          if i.val < 31 then
            1026883452929
          else
            442634207232
        else
          if i.val < 33 then
            17217049633
          else
            if i.val < 34 then
              8945672
            else
              17219023911
      else
        if i.val < 37 then
          if i.val < 36 then
            11452424
          else
            387565903010
        else
          if i.val < 38 then
            154656429089
          else
            if i.val < 39 then
              802567249060
            else
              292094727209

private def fivePackedRows (i : Fin 40) : ℕ :=
  if i.val < 20 then
    if i.val < 10 then
      if i.val < 5 then
        if i.val < 2 then
          if i.val < 1 then
            99612210156282775793292556843998264171848863405123305472
          else
            6845298958456217135364671799438578105798783904180064741174320037888
        else
          if i.val < 3 then
            28038344533836665386453695690500415900907148772443435220964977475059712
          else
            if i.val < 4 then
              20769188672079349799502260216004608
            else
              99612210157732678124858645124200087769162735941968990209
      else
        if i.val < 7 then
          if i.val < 6 then
            6845298958456217135364694105628294507156940855312331112910900166657
          else
            28038344559553951196707162542944774566873219361308064541306633116975168
        else
          if i.val < 8 then
            105312291670089682238784264991193275575704377383386749363017486336
          else
            if i.val < 9 then
              24319387245186224558909394844561463711693786036043840
            else
              1671215566029349886585941322562572796151943617646180355822059521
    else
      if i.val < 15 then
        if i.val < 12 then
          if i.val < 11 then
            374144419156711147384661870833868967072844566495296
          else
            431359146674411769216059113830496081567223634540009577558893601492992
        else
          if i.val < 13 then
            99636535480878363674644571362084296031195986949841092608
          else
            if i.val < 14 then
              6846970582033859285385485089340925423403724041946720750283786289152
            else
              28038344533836665386453695690500415900907148772443510160862776920113152
      else
        if i.val < 17 then
          if i.val < 16 then
            431359146674410236714672241392314111547383002182813225955489382137856
          else
            99636535482328266092610479368305651367257318404908908544
        else
          if i.val < 18 then
            6846970582033859285385485089340925423403724041946720754751626018816
          else
            if i.val < 19 then
              28038344559553951196332926779935645167788958079214860434846325902671872
            else
              431464459367813304966117728305488305064992548210995978416167915094016
  else
    if i.val < 30 then
      if i.val < 25 then
        if i.val < 22 then
          if i.val < 21 then
            99612210157732678124858645124200087769162735941968723968
          else
            6845298958456217135364671799438578105798783904180064745641086025728
        else
          if i.val < 23 then
            28038344559553951196332926779935645167788958079214785476934127948136448
          else
            if i.val < 24 then
              105312291668557186697918027683691201507567476981803517240540135424
            else
              99636535482328266092610479368305651367257318404909174849
      else
        if i.val < 27 then
          if i.val < 26 then
            6846970582033859285385507395531971052757665908951890929081720504321
          else
            28038344559553951196707162542944774566873219361308139499500306048221248
        else
          if i.val < 28 then
            431464459367814837467504601092119418811875424442262693726914122616832
          else
            if i.val < 29 then
              79228162514264337593543950336
            else
              5070602400912917605986812821504
    else
      if i.val < 35 then
        if i.val < 32 then
          if i.val < 31 then
            324518553658426726783156020576256
          else
            20769187434139310514121985316880384
        else
          if i.val < 33 then
            24319388694734748863219625063914890181296202163945537
          else
            if i.val < 34 then
              1671215566029349886585941322562572796151943617646184754959089665
            else
              25711008708517988827828189695434993745804982729263787456593984
      else
        if i.val < 37 then
          if i.val < 36 then
            431464459367814837467504601092119418811874166852456473126045489303552
          else
            24319388694734748863219625063914890181296202163683328
        else
          if i.val < 38 then
            1671215566029349886563640576034814177225492026469729333155987456
          else
            if i.val < 39 then
              25711008708143844408671393477783120194013748432298535806828544
            else
              431464459367813304966117728305488305064991290625912124298168926994432

private def fivePackedQuotients (i : Fin 40) : ℕ :=
  if i.val < 20 then
    if i.val < 10 then
      if i.val < 5 then
        if i.val < 2 then
          if i.val < 1 then
            208351778456651449438825197840437840
          else
            22459812449394606054557360705
        else
          if i.val < 3 then
            11492436760144197000837997065
          else
            if i.val < 4 then
              208351800742336069134003807978070673
            else
              216921819297101489077963272020140042
      else
        if i.val < 7 then
          if i.val < 6 then
            5887682440922525724093730856894464
          else
            213909168417491864117060239402541065
        else
          if i.val < 8 then
            210988501434566023573759485645758473
          else
            if i.val < 9 then
              373855673495279497446230260271087624
            else
              373850523645071016472176918836314112
    else
      if i.val < 15 then
        if i.val < 12 then
          if i.val < 11 then
            192815462429694126603612001915183113
          else
            5892775522440331958495328917331977
        else
          if i.val < 13 then
            42188680866554184219902181806440512
          else
            if i.val < 14 then
              232133617836673622040572965812052105
            else
              253227957649771473684444966854729865
      else
        if i.val < 17 then
          if i.val < 16 then
            144115188075855872
          else
            0
        else
          if i.val < 18 then
            0
          else
            if i.val < 19 then
              0
            else
              0
  else
    if i.val < 30 then
      if i.val < 25 then
        if i.val < 22 then
          if i.val < 21 then
            5887682440927321877552895342710785
          else
            5887704900696596667654432694509569
        else
          if i.val < 23 then
            3012650879609624960903032619732993
          else
            if i.val < 24 then
              211364429162175830161916449147199561
            else
              210988491705169333132495925092328017
      else
        if i.val < 27 then
          if i.val < 26 then
            5933340496394863695924601217954314
          else
            186932907359560957099886752275955720
        else
          if i.val < 28 then
            21418859604696907951885991562182720
          else
            if i.val < 29 then
              379748448998377016272877123883639378
            else
              214234389947007877190596163523388042
    else
      if i.val < 35 then
        if i.val < 32 then
          if i.val < 31 then
            211039909370577364005561895129588306
          else
            211039899467057049722278353134297682
        else
          if i.val < 33 then
            192815462429694126585597604479442953
          else
            if i.val < 34 then
              21093705987797737529210835109675008
            else
              379738228565110435495051862428950537
      else
        if i.val < 37 then
          if i.val < 36 then
            210942843533840914014272591780937728
          else
            235003499567427808767183265920524425
        else
          if i.val < 38 then
            210988501434566023429609113199910921
          else
            if i.val < 39 then
              419330038045414189739897521743929481
            else
              26661962956579642616772094392344585

private theorem five_packed_row_0 :
    fivePackedRows 0 = packedMinorResidueRow fiveMinor 2 64 0 := by rfl

private theorem five_packed_product_0 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 0) fivePackedRows =
      64 ^ (0 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 0) := by rfl

private theorem five_packed_row_1 :
    fivePackedRows 1 = packedMinorResidueRow fiveMinor 2 64 1 := by rfl

private theorem five_packed_product_1 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 1) fivePackedRows =
      64 ^ (1 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 1) := by rfl

private theorem five_packed_row_2 :
    fivePackedRows 2 = packedMinorResidueRow fiveMinor 2 64 2 := by rfl

private theorem five_packed_product_2 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 2) fivePackedRows =
      64 ^ (2 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 2) := by rfl

private theorem five_packed_row_3 :
    fivePackedRows 3 = packedMinorResidueRow fiveMinor 2 64 3 := by rfl

private theorem five_packed_product_3 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 3) fivePackedRows =
      64 ^ (3 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 3) := by rfl

private theorem five_packed_row_4 :
    fivePackedRows 4 = packedMinorResidueRow fiveMinor 2 64 4 := by rfl

private theorem five_packed_product_4 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 4) fivePackedRows =
      64 ^ (4 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 4) := by rfl

private theorem five_packed_row_5 :
    fivePackedRows 5 = packedMinorResidueRow fiveMinor 2 64 5 := by rfl

private theorem five_packed_product_5 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 5) fivePackedRows =
      64 ^ (5 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 5) := by rfl

private theorem five_packed_row_6 :
    fivePackedRows 6 = packedMinorResidueRow fiveMinor 2 64 6 := by rfl

private theorem five_packed_product_6 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 6) fivePackedRows =
      64 ^ (6 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 6) := by rfl

private theorem five_packed_row_7 :
    fivePackedRows 7 = packedMinorResidueRow fiveMinor 2 64 7 := by rfl

private theorem five_packed_product_7 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 7) fivePackedRows =
      64 ^ (7 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 7) := by rfl

private theorem five_packed_row_8 :
    fivePackedRows 8 = packedMinorResidueRow fiveMinor 2 64 8 := by rfl

private theorem five_packed_product_8 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 8) fivePackedRows =
      64 ^ (8 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 8) := by rfl

private theorem five_packed_row_9 :
    fivePackedRows 9 = packedMinorResidueRow fiveMinor 2 64 9 := by rfl

private theorem five_packed_product_9 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 9) fivePackedRows =
      64 ^ (9 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 9) := by rfl

private theorem five_packed_row_10 :
    fivePackedRows 10 = packedMinorResidueRow fiveMinor 2 64 10 := by rfl

private theorem five_packed_product_10 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 10) fivePackedRows =
      64 ^ (10 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 10) := by rfl

private theorem five_packed_row_11 :
    fivePackedRows 11 = packedMinorResidueRow fiveMinor 2 64 11 := by rfl

private theorem five_packed_product_11 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 11) fivePackedRows =
      64 ^ (11 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 11) := by rfl

private theorem five_packed_row_12 :
    fivePackedRows 12 = packedMinorResidueRow fiveMinor 2 64 12 := by rfl

private theorem five_packed_product_12 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 12) fivePackedRows =
      64 ^ (12 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 12) := by rfl

private theorem five_packed_row_13 :
    fivePackedRows 13 = packedMinorResidueRow fiveMinor 2 64 13 := by rfl

private theorem five_packed_product_13 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 13) fivePackedRows =
      64 ^ (13 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 13) := by rfl

private theorem five_packed_row_14 :
    fivePackedRows 14 = packedMinorResidueRow fiveMinor 2 64 14 := by rfl

private theorem five_packed_product_14 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 14) fivePackedRows =
      64 ^ (14 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 14) := by rfl

private theorem five_packed_row_15 :
    fivePackedRows 15 = packedMinorResidueRow fiveMinor 2 64 15 := by rfl

private theorem five_packed_product_15 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 15) fivePackedRows =
      64 ^ (15 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 15) := by rfl

private theorem five_packed_row_16 :
    fivePackedRows 16 = packedMinorResidueRow fiveMinor 2 64 16 := by rfl

private theorem five_packed_product_16 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 16) fivePackedRows =
      64 ^ (16 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 16) := by rfl

private theorem five_packed_row_17 :
    fivePackedRows 17 = packedMinorResidueRow fiveMinor 2 64 17 := by rfl

private theorem five_packed_product_17 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 17) fivePackedRows =
      64 ^ (17 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 17) := by rfl

private theorem five_packed_row_18 :
    fivePackedRows 18 = packedMinorResidueRow fiveMinor 2 64 18 := by rfl

private theorem five_packed_product_18 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 18) fivePackedRows =
      64 ^ (18 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 18) := by rfl

private theorem five_packed_row_19 :
    fivePackedRows 19 = packedMinorResidueRow fiveMinor 2 64 19 := by rfl

private theorem five_packed_product_19 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 19) fivePackedRows =
      64 ^ (19 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 19) := by rfl

private theorem five_packed_row_20 :
    fivePackedRows 20 = packedMinorResidueRow fiveMinor 2 64 20 := by rfl

private theorem five_packed_product_20 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 20) fivePackedRows =
      64 ^ (20 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 20) := by rfl

private theorem five_packed_row_21 :
    fivePackedRows 21 = packedMinorResidueRow fiveMinor 2 64 21 := by rfl

private theorem five_packed_product_21 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 21) fivePackedRows =
      64 ^ (21 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 21) := by rfl

private theorem five_packed_row_22 :
    fivePackedRows 22 = packedMinorResidueRow fiveMinor 2 64 22 := by rfl

private theorem five_packed_product_22 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 22) fivePackedRows =
      64 ^ (22 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 22) := by rfl

private theorem five_packed_row_23 :
    fivePackedRows 23 = packedMinorResidueRow fiveMinor 2 64 23 := by rfl

private theorem five_packed_product_23 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 23) fivePackedRows =
      64 ^ (23 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 23) := by rfl

private theorem five_packed_row_24 :
    fivePackedRows 24 = packedMinorResidueRow fiveMinor 2 64 24 := by rfl

private theorem five_packed_product_24 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 24) fivePackedRows =
      64 ^ (24 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 24) := by rfl

private theorem five_packed_row_25 :
    fivePackedRows 25 = packedMinorResidueRow fiveMinor 2 64 25 := by rfl

private theorem five_packed_product_25 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 25) fivePackedRows =
      64 ^ (25 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 25) := by rfl

private theorem five_packed_row_26 :
    fivePackedRows 26 = packedMinorResidueRow fiveMinor 2 64 26 := by rfl

private theorem five_packed_product_26 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 26) fivePackedRows =
      64 ^ (26 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 26) := by rfl

private theorem five_packed_row_27 :
    fivePackedRows 27 = packedMinorResidueRow fiveMinor 2 64 27 := by rfl

private theorem five_packed_product_27 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 27) fivePackedRows =
      64 ^ (27 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 27) := by rfl

private theorem five_packed_row_28 :
    fivePackedRows 28 = packedMinorResidueRow fiveMinor 2 64 28 := by rfl

private theorem five_packed_product_28 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 28) fivePackedRows =
      64 ^ (28 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 28) := by rfl

private theorem five_packed_row_29 :
    fivePackedRows 29 = packedMinorResidueRow fiveMinor 2 64 29 := by rfl

private theorem five_packed_product_29 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 29) fivePackedRows =
      64 ^ (29 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 29) := by rfl

private theorem five_packed_row_30 :
    fivePackedRows 30 = packedMinorResidueRow fiveMinor 2 64 30 := by rfl

private theorem five_packed_product_30 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 30) fivePackedRows =
      64 ^ (30 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 30) := by rfl

private theorem five_packed_row_31 :
    fivePackedRows 31 = packedMinorResidueRow fiveMinor 2 64 31 := by rfl

private theorem five_packed_product_31 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 31) fivePackedRows =
      64 ^ (31 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 31) := by rfl

private theorem five_packed_row_32 :
    fivePackedRows 32 = packedMinorResidueRow fiveMinor 2 64 32 := by rfl

private theorem five_packed_product_32 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 32) fivePackedRows =
      64 ^ (32 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 32) := by rfl

private theorem five_packed_row_33 :
    fivePackedRows 33 = packedMinorResidueRow fiveMinor 2 64 33 := by rfl

private theorem five_packed_product_33 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 33) fivePackedRows =
      64 ^ (33 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 33) := by rfl

private theorem five_packed_row_34 :
    fivePackedRows 34 = packedMinorResidueRow fiveMinor 2 64 34 := by rfl

private theorem five_packed_product_34 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 34) fivePackedRows =
      64 ^ (34 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 34) := by rfl

private theorem five_packed_row_35 :
    fivePackedRows 35 = packedMinorResidueRow fiveMinor 2 64 35 := by rfl

private theorem five_packed_product_35 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 35) fivePackedRows =
      64 ^ (35 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 35) := by rfl

private theorem five_packed_row_36 :
    fivePackedRows 36 = packedMinorResidueRow fiveMinor 2 64 36 := by rfl

private theorem five_packed_product_36 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 36) fivePackedRows =
      64 ^ (36 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 36) := by rfl

private theorem five_packed_row_37 :
    fivePackedRows 37 = packedMinorResidueRow fiveMinor 2 64 37 := by rfl

private theorem five_packed_product_37 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 37) fivePackedRows =
      64 ^ (37 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 37) := by rfl

private theorem five_packed_row_38 :
    fivePackedRows 38 = packedMinorResidueRow fiveMinor 2 64 38 := by rfl

private theorem five_packed_product_38 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 38) fivePackedRows =
      64 ^ (38 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 38) := by rfl

private theorem five_packed_row_39 :
    fivePackedRows 39 = packedMinorResidueRow fiveMinor 2 64 39 := by rfl

private theorem five_packed_product_39 :
    packedProduct (inverseSparseRow 2 fivePackedInverse 39) fivePackedRows =
      64 ^ (39 : Fin 40).val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients 39) := by rfl

private theorem five_packed_rows (i : Fin 40) :
    fivePackedRows i = packedMinorResidueRow fiveMinor 2 64 i := by
  fin_cases i
  · exact five_packed_row_0
  · exact five_packed_row_1
  · exact five_packed_row_2
  · exact five_packed_row_3
  · exact five_packed_row_4
  · exact five_packed_row_5
  · exact five_packed_row_6
  · exact five_packed_row_7
  · exact five_packed_row_8
  · exact five_packed_row_9
  · exact five_packed_row_10
  · exact five_packed_row_11
  · exact five_packed_row_12
  · exact five_packed_row_13
  · exact five_packed_row_14
  · exact five_packed_row_15
  · exact five_packed_row_16
  · exact five_packed_row_17
  · exact five_packed_row_18
  · exact five_packed_row_19
  · exact five_packed_row_20
  · exact five_packed_row_21
  · exact five_packed_row_22
  · exact five_packed_row_23
  · exact five_packed_row_24
  · exact five_packed_row_25
  · exact five_packed_row_26
  · exact five_packed_row_27
  · exact five_packed_row_28
  · exact five_packed_row_29
  · exact five_packed_row_30
  · exact five_packed_row_31
  · exact five_packed_row_32
  · exact five_packed_row_33
  · exact five_packed_row_34
  · exact five_packed_row_35
  · exact five_packed_row_36
  · exact five_packed_row_37
  · exact five_packed_row_38
  · exact five_packed_row_39

private theorem five_packed_products (i : Fin 40) :
    packedProduct (inverseSparseRow 2 fivePackedInverse i) fivePackedRows =
      64 ^ i.val + 2 * Nat.ofDigits 64
        (inverseQuotientRow 8 fivePackedQuotients i) := by
  fin_cases i
  · exact five_packed_product_0
  · exact five_packed_product_1
  · exact five_packed_product_2
  · exact five_packed_product_3
  · exact five_packed_product_4
  · exact five_packed_product_5
  · exact five_packed_product_6
  · exact five_packed_product_7
  · exact five_packed_product_8
  · exact five_packed_product_9
  · exact five_packed_product_10
  · exact five_packed_product_11
  · exact five_packed_product_12
  · exact five_packed_product_13
  · exact five_packed_product_14
  · exact five_packed_product_15
  · exact five_packed_product_16
  · exact five_packed_product_17
  · exact five_packed_product_18
  · exact five_packed_product_19
  · exact five_packed_product_20
  · exact five_packed_product_21
  · exact five_packed_product_22
  · exact five_packed_product_23
  · exact five_packed_product_24
  · exact five_packed_product_25
  · exact five_packed_product_26
  · exact five_packed_product_27
  · exact five_packed_product_28
  · exact five_packed_product_29
  · exact five_packed_product_30
  · exact five_packed_product_31
  · exact five_packed_product_32
  · exact five_packed_product_33
  · exact five_packed_product_34
  · exact five_packed_product_35
  · exact five_packed_product_36
  · exact five_packed_product_37
  · exact five_packed_product_38
  · exact five_packed_product_39

private theorem five_det_ne_zero :
    (fiveMinor.map (Int.castRingHom (ZMod 2))).det ≠ 0 :=
  determinant_ne_zero_of_packed_left_inverse fiveMinor 2 64 8
    (by decide) (by decide) (by decide) (by decide)
    fivePackedInverse fivePackedRows fivePackedQuotients
    five_packed_rows five_packed_products

/-- The integral critical point count in 5 variables. -/
theorem five_idealGenerationAt {K : Type*} [Field K] [CharZero K] :
    IdealGenerationAt K 4 2 10 :=
  idealGenerationAt_of_quadratic_minor_surjective (by decide)
    fivePoints fiveRows fiveCols 2 five_det_ne_zero (by decide)

/-- General quadrics in 5 homogeneous variables have the required rank. -/
theorem quadratic_five_all {K : Type*} [Field K] [CharZero K] :
    ∀ p, IdealGenerationAt K 4 2 p := by
  have he : E 5 2 = 5 := by norm_num [E, N, Nat.choose]
  have hl : lowerCritical 5 2 = 5 := by simp [lowerCritical, he]
  have hu : upperCritical 5 2 = 5 := by simp [upperCritical, he]
  apply idealGenerationAt_all_of_critical (by decide : 1 ≤ 4) (by decide : 1 ≤ 2)
  · change IdealGenerationAt K 4 2 (N 5 2 - lowerCritical 5 2)
    rw [hl, show N 5 2 = 15 by decide]
    exact five_idealGenerationAt
  · change IdealGenerationAt K 4 2 (N 5 2 - upperCritical 5 2)
    rw [hu, show N 5 2 = 15 by decide]
    exact five_idealGenerationAt

end IdealGeneration.QuadraticLowDimension
