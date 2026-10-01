-- Prove2me | Theorems.Thm_syracuse_descent_residual_seven_mod32_mod16777216
-- name    : syracuse_descent_residual_seven_mod32_mod16777216
-- status  : Open
-- author  : @Sneed
-- created : 2026-10-01T08:10:29.068987+00:00
-- url     : https://prove2.me/theorems/45a0800b-e750-4c32-bc04-98c579509977
-- title:
--   Residual Syracuse descent modulo $2^{24}$ after chunked certificate removal
-- statement:
--   Refine the hard residual from modulus $2^{23}$ to $2^{24}=16777216$ and remove 5676 newly certified classes, represented by 9 moderate reusable certificate chunks. The unresolved complement contains 66646 of the 72322 lifted parent classes, removing 7.85% of this stage's residual density.
-- source:
--   Recursive exact refinement of Prove2Me residual theorem bbda9a87-e550-446e-873c-36c10f3e5164; finite children are Terras-style uniform descent certificates.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Definitions.Def_syracuseSevenMod32New21Step11Classes
import Definitions.Def_syracuseSevenMod32New21Step12Classes
import Definitions.Def_syracuseSevenMod32New22Step11Classes
import Definitions.Def_syracuseSevenMod32New22Step12Classes
import Definitions.Def_syracuseSevenMod32New22Step13Classes
import Definitions.Def_syracuseSevenMod32New23Step11Chunk01Classes
import Definitions.Def_syracuseSevenMod32New23Step12Chunk01Classes
import Definitions.Def_syracuseSevenMod32New23Step13Chunk01Classes
import Definitions.Def_syracuseSevenMod32New23Step13Chunk02Classes
import Definitions.Def_syracuseSevenMod32New24Step11Chunk01Classes
import Definitions.Def_syracuseSevenMod32New24Step12Chunk01Classes
import Definitions.Def_syracuseSevenMod32New24Step13Chunk01Classes
import Definitions.Def_syracuseSevenMod32New24Step13Chunk02Classes
import Definitions.Def_syracuseSevenMod32New24Step14Chunk01Classes
import Definitions.Def_syracuseSevenMod32New24Step14Chunk02Classes
import Definitions.Def_syracuseSevenMod32New24Step14Chunk03Classes
import Definitions.Def_syracuseSevenMod32New24Step14Chunk04Classes
import Definitions.Def_syracuseSevenMod32New24Step14Chunk05Classes
set_option autoImplicit false
set_option maxRecDepth 200000

theorem syracuse_descent_residual_seven_mod32_mod16777216 (n : ℕ)
    (h : n % 128 = 39 ∨ n % 128 = 71 ∨ n % 128 = 103)
    (h256 : n % 256 ≠ 39 ∧ n % 256 ≠ 199)
    (h1024 : n % 1024 ≠ 423 ∧ n % 1024 ≠ 583 ∧ n % 1024 ≠ 999)
    (h4096 : n % 4096 ≠ 231 ∧ n % 4096 ≠ 615 ∧ n % 4096 ≠ 935 ∧ n % 4096 ≠ 1703 ∧ n % 4096 ≠ 3143 ∧ n % 4096 ≠ 3559 ∧ n % 4096 ≠ 3911)
    (h8192 : n % 8192 ∉ ({679, 1191, 2663, 3687, 4199, 4455, 5191, 5607, 5959, 6215,
      6375, 6631, 6983, 7079, 7399, 7495, 7847, 7911, 8103} : Finset ℕ))
    (h32768 : n % 32768 ∉ ({839, 1095, 2119, 2279, 2727, 2983, 3303, 4007, 6503, 6759,
      7783, 9959, 10055, 11079, 11943, 12967, 14439, 16743, 16871, 17735,
      17767, 19623, 20199, 21223, 23399, 24647, 24679, 25703, 25831, 26087,
      26535, 27111, 27975, 28999, 29863, 30311, 30887} : Finset ℕ))
    (h65536 : n % 65536 ∉ ({359, 1351, 2407, 2791, 2887, 3239, 3815, 4775, 5863, 6247,
      7015, 8263, 8551, 9319, 9543, 10151, 10727, 11431, 12007, 12615,
      12775, 13671, 13927, 14503, 15207, 16455, 17127, 17223, 17479, 17511,
      18343, 18919, 19111, 19367, 19687, 20807, 21735, 22119, 22695, 22887,
      23143, 25415, 25671, 26343, 26439, 27303, 27559, 27879, 28327, 31079,
      31335, 33255, 34151, 34535, 34631, 36519, 37607, 37735, 40039, 41063,
      41447, 42215, 42343, 42471, 43111, 43335, 44359, 45223, 45799, 46247,
      46407, 48295, 49255, 50407, 50663, 51271, 51431, 52071, 52551, 53159,
      53319, 54375, 54439, 55207, 56935, 57671, 58983, 59463, 59559, 59623,
      60231, 61351, 62119, 62279, 63335, 63591, 64167, 64871, 65127} : Finset ℕ))
    (h524288 : n % 524288 ∉ ({
          6055, 12199, 13031, 17639, 20391, 20551, 24423, 25447, 26695, 26855, 27495, 30055, 30567,
          31591, 32103, 35175, 39783, 41319, 55463, 59719, 60071, 62791, 68935, 69287, 74215,
          77127, 80999, 83431, 84071, 87143, 88167, 91751, 96359, 97895, 109287, 112359, 115431,
          116455, 116647, 120039, 124647, 125863, 126183, 133991, 136039, 140647, 151719, 154791,
          157863, 158887, 162119, 162471, 164167, 167079, 168263, 168615, 168775, 172871, 173383,
          176455, 176615, 181063, 182087, 182759, 187495, 190279, 190567, 196711, 204903, 215783,
          218855, 219047, 224999, 225191, 225351, 229447, 233191, 235367, 236903, 237639, 238663,
          239975, 243047, 244071, 244583, 246855, 252263, 258215, 261287, 267431, 270663, 272711,
          275271, 275623, 275783, 281415, 281927, 289607, 289895, 291943, 296039, 296551, 300647,
          301159, 304231, 308839, 309863, 318055, 318183, 320231, 324327, 324839, 328935, 329447,
          331847, 332519, 337127, 337991, 338151, 340839, 341863, 343399, 346183, 346343, 346471,
          346983, 352615, 360615, 360807, 362663, 366759, 367271, 371367, 371879, 374951, 379559,
          380583, 381255, 381415, 385511, 385863, 388775, 393703, 394727, 395079, 398439, 400487,
          402919, 403047, 403559, 409191, 409703, 417383, 423847, 426727, 427943, 428775, 431335,
          431847, 436135, 437159, 437479, 437991, 442439, 444263, 445351, 445671, 445799, 447335,
          447847, 451655, 451943, 457063, 460135, 469159, 471207, 473767, 474279, 477511, 479911,
          480423, 480583, 483655, 484679, 487911, 488103, 488263, 492871, 494055, 494407, 502247,
          509031, 513639, 522855
        } : Finset ℕ))
    (h1048576 : n % 1048576 ∉ ({
          5287, 8519, 10567, 13479, 13639, 19783, 27751, 29799, 33895, 39015, 42087, 56039, 58087,
          62183, 67303, 70375, 81255, 84327, 90471, 98663, 105127, 109223, 117415, 118439, 123719,
          126631, 132935, 140903, 147047, 155239, 161703, 165799, 169191, 173991, 175015, 175335,
          180295, 182119, 183207, 183527, 185191, 189511, 207015, 209063, 212135, 215367, 218279,
          218439, 221511, 222535, 225767, 230727, 231911, 240103, 246887, 275175, 292199, 294247,
          297319, 303463, 322215, 331431, 353895, 360039, 378791, 382183, 388007, 388327, 396135,
          398183, 413863, 416935, 420007, 421031, 424263, 426311, 429223, 430407, 435527, 438599,
          438759, 444903, 449639, 452711, 458855, 467047, 477927, 480999, 487143, 495335, 499047,
          502119, 505191, 506215, 514407, 537415, 543559, 551751, 558695, 562791, 570983, 572007,
          580199, 586983, 591079, 593991, 599271, 600135, 600295, 602983, 604007, 608327, 608487,
          609127, 622759, 624807, 628903, 634023, 637095, 643399, 643559, 647655, 655847, 656871,
          660583, 662631, 665063, 665703, 671847, 688871, 690919, 693991, 700135, 707943, 709991,
          714087, 719207, 722279, 735911, 742055, 750247, 750407, 756551, 775783, 784999, 792487,
          798631, 804071, 806823, 806983, 810855, 811879, 813127, 813287, 813927, 816999, 818023,
          826215, 841895, 846151, 849223, 855367, 860647, 863559, 867431, 869863, 870503, 873575,
          874599, 882791, 895719, 898791, 901863, 902887, 911079, 927079, 948903, 955047, 955207,
          959303, 967495, 968519, 976711, 1005479, 1011623, 1011783, 1015879, 1021799, 1024071,
          1025095, 1031015, 1033287, 1044647, 1047719
        } : Finset ℕ))
    (h21_11 : n % 2097152 ∉ syracuseSevenMod32New21Step11Classes)
    (h21_12 : n % 2097152 ∉ syracuseSevenMod32New21Step12Classes)
    (h22_11 : n % 4194304 ∉ syracuseSevenMod32New22Step11Classes)
    (h22_12 : n % 4194304 ∉ syracuseSevenMod32New22Step12Classes)
    (h22_13 : n % 4194304 ∉ syracuseSevenMod32New22Step13Classes)
    (h23_11_01 : n % 8388608 ∉ syracuseSevenMod32New23Step11Chunk01Classes)
    (h23_12_01 : n % 8388608 ∉ syracuseSevenMod32New23Step12Chunk01Classes)
    (h23_13_01 : n % 8388608 ∉ syracuseSevenMod32New23Step13Chunk01Classes)
    (h23_13_02 : n % 8388608 ∉ syracuseSevenMod32New23Step13Chunk02Classes)
    (h24_11_01 : n % 16777216 ∉ syracuseSevenMod32New24Step11Chunk01Classes)
    (h24_12_01 : n % 16777216 ∉ syracuseSevenMod32New24Step12Chunk01Classes)
    (h24_13_01 : n % 16777216 ∉ syracuseSevenMod32New24Step13Chunk01Classes)
    (h24_13_02 : n % 16777216 ∉ syracuseSevenMod32New24Step13Chunk02Classes)
    (h24_14_01 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk01Classes)
    (h24_14_02 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk02Classes)
    (h24_14_03 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk03Classes)
    (h24_14_04 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk04Classes)
    (h24_14_05 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk05Classes) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry
