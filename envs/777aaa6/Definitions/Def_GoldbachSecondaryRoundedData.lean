-- Prove2me | Definitions.Def_GoldbachSecondaryRoundedData
-- name    : GoldbachSecondaryRoundedData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-05T02:54:07.09069+00:00
-- url     : https://prove2.me/theorems/968adc2d-b299-4fef-adb2-e0a7a6192b1f
-- title:
--   Conservative integer-grid data for all sixteen secondary optimization rows
-- statement:
--   This definition supplies a fixed family of sixteen integer cap-and-budget records for the secondary branches in [Lorenzo Schiavone's Goldbach certificate release](https://goldbach-nine.vercel.app/). The source witness is `secondary-aligned-witness.json`, identified by SHA-256 `94cff613c74ac36eac9129e5f61ea80dbeb45ef7ca828d8744af42eb6a489d62`.
--
--   Each record contains two finite cap prefixes, repeated tail caps, two mass budgets, and a prefix length. All integer values use the common scale
--   $$D=10^{12}.$$
--   Thus an integer cap $A_i$ represents the real cap $A_i/D$, and a budget $U$ represents $U/D$. The values were formed by exact rational upward rounding. The repeated tails are conservative enlargements of the source tails, and each chosen prefix covers both rounded budgets.
--
--   The sixteen records preserve the exact secondary row inventory. Their strict optimization ceiling is established separately, rather than assumed by this definition. Exact Python comparisons to the frozen source witness are recorded locally; the definition does not prove the analytic derivation of that witness or an exceptional-set estimate.
--
--   Formalization note: The lightweight module contains only data, types, and lookup functions in Mathlib revision `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`.
-- source:
--   Derived numerical data from https://goldbach-nine.vercel.app/release/goldbach-exception-069697-certificate-v4.zip , secondary-aligned-witness.json SHA256 94cff613c74ac36eac9129e5f61ea80dbeb45ef7ca828d8744af42eb6a489d62. Exact upward enclosures checked in Python; no analytic input derivation is claimed.

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.GetD
set_option autoImplicit false

namespace GoldbachSecondaryRoundedData

structure Row where
  rCaps : List ℕ
  tCaps : List ℕ
  rTail : ℕ
  tTail : ℕ
  rBudget : ℕ
  tBudget : ℕ
  prefixLength : ℕ

def scale : ℕ := 1000000000000

-- Frozen witness row: s60-62-n085-le1-m1k1
def row0 : Row where
  rCaps := List.replicate 1 263691439770 ++ List.replicate 87 194473197058
  tCaps := List.replicate 1 104092124632 ++ List.replicate 7 98032979064 ++ List.replicate 1 97180865788 ++ List.replicate 1 96361674368 ++ List.replicate 1 95962281398 ++ List.replicate 1 95182307995 ++ List.replicate 1 94807233965 ++ List.replicate 2 94437025868 ++ List.replicate 1 93969442137 ++ List.replicate 2 93469282934 ++ List.replicate 1 92966875355 ++ List.replicate 3 92486445228 ++ List.replicate 2 92001376864 ++ List.replicate 4 91529099965 ++ List.replicate 4 91062492652 ++ List.replicate 5 90612751433 ++ List.replicate 7 90152012248 ++ List.replicate 11 89717757950 ++ List.replicate 16 89280537208 ++ List.replicate 17 88850946833
  rTail := 194473197058
  tTail := 88850946833
  rBudget := 583534647833
  tBudget := 7973860264511
  prefixLength := 88

-- Frozen witness row: s60-62-n091-le2-m1k1
def row1 : Row where
  rCaps := List.replicate 1 249870675749 ++ List.replicate 87 170289442027
  tCaps := List.replicate 1 104092124632 ++ List.replicate 8 96765366935 ++ List.replicate 1 96361674368 ++ List.replicate 1 95962281398 ++ List.replicate 1 95182307995 ++ List.replicate 1 94807233965 ++ List.replicate 2 94437025868 ++ List.replicate 1 93969442137 ++ List.replicate 2 93469282934 ++ List.replicate 1 92966875355 ++ List.replicate 3 92486445228 ++ List.replicate 2 92001376864 ++ List.replicate 4 91529099965 ++ List.replicate 4 91062492652 ++ List.replicate 5 90612751433 ++ List.replicate 7 90152012248 ++ List.replicate 11 89717757950 ++ List.replicate 16 89280537208 ++ List.replicate 17 88850946833
  rTail := 170289442027
  tTail := 88850946833
  rBudget := 542941730151
  tBudget := 7973860264511
  prefixLength := 88

-- Frozen witness row: s60-62-n091-le2-m2k1
def row2 : Row where
  rCaps := List.replicate 1 305171373786 ++ List.replicate 87 170289442027
  tCaps := List.replicate 1 104092124632 ++ List.replicate 7 96765366935 ++ List.replicate 1 96361674368 ++ List.replicate 1 95570052421 ++ List.replicate 1 95182307995 ++ List.replicate 1 94807233965 ++ List.replicate 1 94437025868 ++ List.replicate 1 93969442137 ++ List.replicate 2 93469282934 ++ List.replicate 1 92966875355 ++ List.replicate 2 92486445228 ++ List.replicate 3 92001376864 ++ List.replicate 3 91529099965 ++ List.replicate 3 91062492652 ++ List.replicate 5 90612751433 ++ List.replicate 7 90152012248 ++ List.replicate 9 89717757950 ++ List.replicate 15 89280537208 ++ List.replicate 24 88850946833
  rTail := 170289442027
  tTail := 88850946833
  rBudget := 592935826741
  tBudget := 7973860264511
  prefixLength := 88

-- Frozen witness row: s60-62-n091-le2-m2k2
def row3 : Row where
  rCaps := List.replicate 2 249870675749 ++ List.replicate 86 170289442027
  tCaps := List.replicate 2 104092124632 ++ List.replicate 7 96765366935 ++ List.replicate 1 96361674368 ++ List.replicate 1 95570052421 ++ List.replicate 1 95182307995 ++ List.replicate 1 94807233965 ++ List.replicate 1 94437025868 ++ List.replicate 1 93969442137 ++ List.replicate 2 93469282934 ++ List.replicate 1 92966875355 ++ List.replicate 2 92486445228 ++ List.replicate 3 92001376864 ++ List.replicate 3 91529099965 ++ List.replicate 3 91062492652 ++ List.replicate 5 90612751433 ++ List.replicate 7 90152012248 ++ List.replicate 9 89717757950 ++ List.replicate 15 89280537208 ++ List.replicate 23 88850946833
  rTail := 170289442027
  tTail := 88850946833
  rBudget := 592935826741
  tBudget := 7973860264511
  prefixLength := 88

-- Frozen witness row: s62-64-n085-le2-m1k1
def row4 : Row where
  rCaps := List.replicate 1 257551516965 ++ List.replicate 87 196229781837
  tCaps := List.replicate 1 101948468618 ++ List.replicate 7 96424271193 ++ List.replicate 1 95576959607 ++ List.replicate 1 94760634484 ++ List.replicate 1 94358671808 ++ List.replicate 1 93580735150 ++ List.replicate 1 93204990276 ++ List.replicate 1 92830443562 ++ List.replicate 2 92467389700 ++ List.replicate 1 92105848459 ++ List.replicate 2 91630956760 ++ List.replicate 2 91146867663 ++ List.replicate 3 90660995827 ++ List.replicate 3 90189310481 ++ List.replicate 4 89732063226 ++ List.replicate 5 89272828596 ++ List.replicate 6 88825388919 ++ List.replicate 9 88377744438 ++ List.replicate 14 87941336469 ++ List.replicate 22 87515474789 ++ List.replicate 1 87090048014
  rTail := 196229781837
  tTail := 87090048014
  rBudget := 571995754782
  tBudget := 7886243705354
  prefixLength := 88

-- Frozen witness row: s62-64-n085-le2-m2k1
def row5 : Row where
  rCaps := List.replicate 1 298859685364 ++ List.replicate 88 196229781837
  tCaps := List.replicate 1 101948468618 ++ List.replicate 6 96424271193 ++ List.replicate 1 95161995756 ++ List.replicate 1 94760634484 ++ List.replicate 1 93968252605 ++ List.replicate 1 93580735150 ++ List.replicate 1 92830443562 ++ List.replicate 2 92467389700 ++ List.replicate 1 92105848459 ++ List.replicate 1 91630956760 ++ List.replicate 2 91146867663 ++ List.replicate 3 90660995827 ++ List.replicate 2 90189310481 ++ List.replicate 4 89732063226 ++ List.replicate 4 89272828596 ++ List.replicate 6 88825388919 ++ List.replicate 8 88377744438 ++ List.replicate 12 87941336469 ++ List.replicate 20 87515474789 ++ List.replicate 12 87090048014
  rTail := 196229781837
  tTail := 87090048014
  rBudget := 609164140110
  tBudget := 7886243705354
  prefixLength := 89

-- Frozen witness row: s62-64-n085-le2-m2k2
def row6 : Row where
  rCaps := List.replicate 2 257551516965 ++ List.replicate 86 196229781837
  tCaps := List.replicate 2 101948468618 ++ List.replicate 6 96424271193 ++ List.replicate 1 95161995756 ++ List.replicate 1 94760634484 ++ List.replicate 1 93968252605 ++ List.replicate 1 93580735150 ++ List.replicate 1 92830443562 ++ List.replicate 2 92467389700 ++ List.replicate 1 92105848459 ++ List.replicate 1 91630956760 ++ List.replicate 2 91146867663 ++ List.replicate 3 90660995827 ++ List.replicate 2 90189310481 ++ List.replicate 4 89732063226 ++ List.replicate 4 89272828596 ++ List.replicate 6 88825388919 ++ List.replicate 8 88377744438 ++ List.replicate 12 87941336469 ++ List.replicate 20 87515474789 ++ List.replicate 10 87090048014
  rTail := 196229781837
  tTail := 87090048014
  rBudget := 609164140110
  tBudget := 7886243705354
  prefixLength := 88

-- Frozen witness row: s64-66-m1k1
def row7 : Row where
  rCaps := List.replicate 1 284140670669 ++ List.replicate 88 254323153654
  tCaps := List.replicate 1 99636565409 ++ List.replicate 3 97131893460 ++ List.replicate 4 94490317292 ++ List.replicate 1 93648068272 ++ List.replicate 1 92827159672 ++ List.replicate 1 92430718478 ++ List.replicate 1 92047158115 ++ List.replicate 1 91284515091 ++ List.replicate 2 90916690523 ++ List.replicate 1 90553836193 ++ List.replicate 1 90197881028 ++ List.replicate 2 89841228904 ++ List.replicate 2 89485991974 ++ List.replicate 3 89017357731 ++ List.replicate 3 88539884901 ++ List.replicate 4 88083826360 ++ List.replicate 5 87623685170 ++ List.replicate 7 87177177485 ++ List.replicate 9 86736795800 ++ List.replicate 13 86302309632 ++ List.replicate 22 85877878712 ++ List.replicate 2 85455281667
  rTail := 254323153654
  tTail := 85455281667
  rBudget := 661064962016
  tBudget := 7792640211761
  prefixLength := 89

-- Frozen witness row: s64-66-m2k1
def row8 : Row where
  rCaps := List.replicate 1 303279052609 ++ List.replicate 88 254323153654
  tCaps := List.replicate 1 99636565409 ++ List.replicate 3 97131893460 ++ List.replicate 2 94490317292 ++ List.replicate 1 94063080515 ++ List.replicate 1 93233263316 ++ List.replicate 1 92430718478 ++ List.replicate 1 91661710229 ++ List.replicate 1 91284515091 ++ List.replicate 1 90916690523 ++ List.replicate 1 90553836193 ++ List.replicate 1 90197881028 ++ List.replicate 2 89841228904 ++ List.replicate 2 89485991974 ++ List.replicate 2 89017357731 ++ List.replicate 3 88539884901 ++ List.replicate 3 88083826360 ++ List.replicate 4 87623685170 ++ List.replicate 6 87177177485 ++ List.replicate 8 86736795800 ++ List.replicate 12 86302309632 ++ List.replicate 19 85877878712 ++ List.replicate 14 85455281667
  rTail := 254323153654
  tTail := 85455281667
  rBudget := 677988643644
  tBudget := 7792640211761
  prefixLength := 89

-- Frozen witness row: s64-66-m2k2
def row9 : Row where
  rCaps := List.replicate 2 284140670669 ++ List.replicate 87 254323153654
  tCaps := List.replicate 2 99636565409 ++ List.replicate 2 97131893460 ++ List.replicate 3 94490317292 ++ List.replicate 1 94063080515 ++ List.replicate 1 93233263316 ++ List.replicate 1 92430718478 ++ List.replicate 1 91661710229 ++ List.replicate 1 91284515091 ++ List.replicate 1 90916690523 ++ List.replicate 1 90553836193 ++ List.replicate 1 90197881028 ++ List.replicate 2 89841228904 ++ List.replicate 2 89485991974 ++ List.replicate 2 89017357731 ++ List.replicate 3 88539884901 ++ List.replicate 3 88083826360 ++ List.replicate 4 87623685170 ++ List.replicate 6 87177177485 ++ List.replicate 8 86736795800 ++ List.replicate 12 86302309632 ++ List.replicate 19 85877878712 ++ List.replicate 13 85455281667
  rTail := 254323153654
  tTail := 85455281667
  rBudget := 677988643644
  tBudget := 7792640211761
  prefixLength := 89

-- Frozen witness row: s66-68-m1k1
def row10 : Row where
  rCaps := List.replicate 1 279574165053 ++ List.replicate 88 256540223132
  tCaps := List.replicate 1 97596596352 ++ List.replicate 3 95615730794 ++ List.replicate 4 92961924932 ++ List.replicate 1 92116770254 ++ List.replicate 1 91305718969 ++ List.replicate 1 90912079073 ++ List.replicate 1 90134875529 ++ List.replicate 1 89761767785 ++ List.replicate 1 89389527571 ++ List.replicate 2 89034282822 ++ List.replicate 1 88669343593 ++ List.replicate 2 88319516896 ++ List.replicate 2 87973643680 ++ List.replicate 2 87640032878 ++ List.replicate 3 87265358196 ++ List.replicate 4 86808922937 ++ List.replicate 4 86352556794 ++ List.replicate 7 85908365289 ++ List.replicate 8 85464369485 ++ List.replicate 12 85035513032 ++ List.replicate 18 84613816711 ++ List.replicate 10 84186457544
  rTail := 256540223132
  tTail := 84186457544
  rBudget := 650035952315
  tBudget := 7707135994544
  prefixLength := 89

-- Frozen witness row: s66-68-m2k1
def row11 : Row where
  rCaps := List.replicate 1 294106593080 ++ List.replicate 89 256540223132
  tCaps := List.replicate 1 97596596352 ++ List.replicate 3 95615730794 ++ List.replicate 2 92961924932 ++ List.replicate 1 92535461752 ++ List.replicate 1 91706225865 ++ List.replicate 1 90912079073 ++ List.replicate 1 90134875529 ++ List.replicate 1 89761767785 ++ List.replicate 1 89389527571 ++ List.replicate 1 89034282822 ++ List.replicate 1 88669343593 ++ List.replicate 2 88319516896 ++ List.replicate 1 87973643680 ++ List.replicate 2 87640032878 ++ List.replicate 3 87265358196 ++ List.replicate 3 86808922937 ++ List.replicate 4 86352556794 ++ List.replicate 5 85908365289 ++ List.replicate 7 85464369485 ++ List.replicate 10 85035513032 ++ List.replicate 16 84613816711 ++ List.replicate 23 84186457544
  rTail := 256540223132
  tTail := 84186457544
  rBudget := 662905939026
  tBudget := 7707135994544
  prefixLength := 90

-- Frozen witness row: s66-68-m2k2
def row12 : Row where
  rCaps := List.replicate 2 279574165053 ++ List.replicate 88 256540223132
  tCaps := List.replicate 2 97596596352 ++ List.replicate 2 95615730794 ++ List.replicate 3 92961924932 ++ List.replicate 1 92535461752 ++ List.replicate 1 91706225865 ++ List.replicate 1 90912079073 ++ List.replicate 1 90134875529 ++ List.replicate 1 89761767785 ++ List.replicate 1 89389527571 ++ List.replicate 1 89034282822 ++ List.replicate 1 88669343593 ++ List.replicate 2 88319516896 ++ List.replicate 1 87973643680 ++ List.replicate 2 87640032878 ++ List.replicate 3 87265358196 ++ List.replicate 3 86808922937 ++ List.replicate 4 86352556794 ++ List.replicate 5 85908365289 ++ List.replicate 7 85464369485 ++ List.replicate 10 85035513032 ++ List.replicate 16 84613816711 ++ List.replicate 22 84186457544
  rTail := 256540223132
  tTail := 84186457544
  rBudget := 662905939026
  tBudget := 7707135994544
  prefixLength := 90

-- Frozen witness row: s68-0702-m1k1
def row13 : Row where
  rCaps := List.replicate 1 289282924758 ++ List.replicate 89 282817005055
  tCaps := List.replicate 1 95381652903 ++ List.replicate 3 94833755317 ++ List.replicate 4 91261859388 ++ List.replicate 1 90413409205 ++ List.replicate 1 89609351852 ++ List.replicate 1 89206600638 ++ List.replicate 1 88440325927 ++ List.replicate 1 88059537904 ++ List.replicate 1 87687863468 ++ List.replicate 1 87325916537 ++ List.replicate 2 86970544529 ++ List.replicate 1 86621435912 ++ List.replicate 2 86276781854 ++ List.replicate 3 85937302093 ++ List.replicate 2 85602417770 ++ List.replicate 4 85274837719 ++ List.replicate 4 84939126151 ++ List.replicate 6 84486865392 ++ List.replicate 7 84047093266 ++ List.replicate 11 83616088066 ++ List.replicate 15 83192746721 ++ List.replicate 18 82769443365
  rTail := 282817005055
  tTail := 82769443365
  rBudget := 689251467506
  tBudget := 7615728241235
  prefixLength := 90

-- Frozen witness row: s68-0702-m2k1
def row14 : Row where
  rCaps := List.replicate 1 293241803165 ++ List.replicate 89 282817005055
  tCaps := List.replicate 1 95381652903 ++ List.replicate 3 94833755317 ++ List.replicate 2 91261859388 ++ List.replicate 1 90839708104 ++ List.replicate 1 89609351852 ++ List.replicate 1 88814694527 ++ List.replicate 1 88440325927 ++ List.replicate 1 88059537904 ++ List.replicate 1 87325916537 ++ List.replicate 2 86970544529 ++ List.replicate 1 86621435912 ++ List.replicate 2 86276781854 ++ List.replicate 2 85937302093 ++ List.replicate 2 85602417770 ++ List.replicate 3 85274837719 ++ List.replicate 3 84939126151 ++ List.replicate 5 84486865392 ++ List.replicate 6 84047093266 ++ List.replicate 9 83616088066 ++ List.replicate 14 83192746721 ++ List.replicate 22 82769443365 ++ List.replicate 7 82358677997
  rTail := 282817005055
  tTail := 82358677997
  rBudget := 692718291874
  tBudget := 7615728241235
  prefixLength := 90

-- Frozen witness row: s68-0702-m2k2
def row15 : Row where
  rCaps := List.replicate 2 289282924758 ++ List.replicate 88 282817005055
  tCaps := List.replicate 2 95381652903 ++ List.replicate 2 94833755317 ++ List.replicate 3 91261859388 ++ List.replicate 1 90839708104 ++ List.replicate 1 89609351852 ++ List.replicate 1 88814694527 ++ List.replicate 1 88440325927 ++ List.replicate 1 88059537904 ++ List.replicate 1 87325916537 ++ List.replicate 2 86970544529 ++ List.replicate 1 86621435912 ++ List.replicate 2 86276781854 ++ List.replicate 2 85937302093 ++ List.replicate 2 85602417770 ++ List.replicate 3 85274837719 ++ List.replicate 3 84939126151 ++ List.replicate 5 84486865392 ++ List.replicate 6 84047093266 ++ List.replicate 9 83616088066 ++ List.replicate 14 83192746721 ++ List.replicate 22 82769443365 ++ List.replicate 6 82358677997
  rTail := 282817005055
  tTail := 82358677997
  rBudget := 692718291874
  tBudget := 7615728241235
  prefixLength := 90

def row : Fin 16 → Row := ![row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15]

def rcap (k : Fin 16) (i : ℕ) : ℕ := (row k).rCaps.getD i (row k).rTail
def tcap (k : Fin 16) (i : ℕ) : ℕ := (row k).tCaps.getD i (row k).tTail

end GoldbachSecondaryRoundedData


