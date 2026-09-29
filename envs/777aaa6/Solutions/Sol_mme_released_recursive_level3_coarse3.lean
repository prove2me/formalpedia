-- Prove2me | solution 1 for mme_released_recursive_level3_coarse3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T10:18:03.22547+00:00
-- url     : https://prove2.me/submissions/124c789a-4f0f-41f4-86db-408f9c91988c

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_floor_data
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3C

theorem cr_1_0 :
    (693147180559618866309328000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (0 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (0 : Fin 88) = fun j => if j.val = 0 then 109638383225826917493 * 499999714324 * 10 ^ 24 else if j.val = 1 then 109638383225826917493 * 500000285676 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_1 :
    (693147180559799692383628000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (1 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (1 : Fin 88) = fun j => if j.val = 0 then 9088980207679028411433 * 499999809201 * 10 ^ 24 else if j.val = 1 then 9088980207679028411433 * 500000190799 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_2 :
    (693147180559936673804048000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (2 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (2 : Fin 88) = fun j => if j.val = 0 then 3507497171920217738522 * 500000046464 * 10 ^ 24 else if j.val = 1 then 3507497171920217738522 * 499999953536 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_3 :
    (693147145124760630225168398787 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (3 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (3 : Fin 88) = fun j => if j.val = 0 then 110610548046162776326 * 500131934035 * 10 ^ 24 else if j.val = 1 then 110610548046162776326 * 499868065965 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_4 :
    (900151104605742571664134942889 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (4 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (4 : Fin 88) = fun j => if j.val = 0 then 2327532889924818009000 * 178900489871 * 10 ^ 24 else if j.val = 1 then 2327532889924818009000 * 642199087952 * 10 ^ 24 else if j.val = 2 then 2327532889924818009000 * 178900422177 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_5 :
    (903985168998886939806454299319 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (5 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else if j.val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (5 : Fin 88) = fun j => if j.val = 0 then 1461435110486930586420 * 180408131762 * 10 ^ 24 else if j.val = 1 then 1461435110486930586420 * 639183737686 * 10 ^ 24 else if j.val = 2 then 1461435110486930586420 * 180408130552 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_6 :
    (911405122907626736707021348512 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (6 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (6 : Fin 88) = fun j => if j.val = 0 then 11511414805550672206280 * 183371061413 * 10 ^ 24 else if j.val = 1 then 11511414805550672206280 * 633257983850 * 10 ^ 24 else if j.val = 2 then 11511414805550672206280 * 183370954737 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_7 :
    (908860533067974456378748142475 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (7 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 6) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (7 : Fin 88) = fun j => if j.val = 0 then 3092428028935533181843 * 182348088415 * 10 ^ 24 else if j.val = 1 then 3092428028935533181843 * 635303846126 * 10 ^ 24 else if j.val = 2 then 3092428028935533181843 * 182348065459 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_8 :
    (810274913600030122887928943948 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (8 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (8 : Fin 88) = fun j => if j.val = 0 then 37962630290561097863440 * 12530154942 * 10 ^ 24 else if j.val = 1 then 37962630290561097863440 * 487469844318 * 10 ^ 24 else if j.val = 2 then 37962630290561097863440 * 487469842409 * 10 ^ 24 else if j.val = 3 then 37962630290561097863440 * 12530158331 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_9 :
    (809309904486167137701404409219 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (9 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else -4) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (9 : Fin 88) = fun j => if j.val = 0 then 37450101734117273001739 * 12398575535 * 10 ^ 24 else if j.val = 1 then 37450101734117273001739 * 487601427168 * 10 ^ 24 else if j.val = 2 then 37450101734117273001739 * 487601456819 * 10 ^ 24 else if j.val = 3 then 37450101734117273001739 * 12398540478 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_10 :
    (812635644499153393521685415167 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (10 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (10 : Fin 88) = fun j => if j.val = 0 then 33031327604148577472310 * 12853781789 * 10 ^ 24 else if j.val = 1 then 33031327604148577472310 * 487146284216 * 10 ^ 24 else if j.val = 2 then 33031327604148577472310 * 487146251242 * 10 ^ 24 else if j.val = 3 then 33031327604148577472310 * 12853682753 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_11 :
    (812708501880274337221076000953 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (11 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (11 : Fin 88) = fun j => if j.val = 0 then 4583319222669465617794 * 12863761495 * 10 ^ 24 else if j.val = 1 then 4583319222669465617794 * 487136239079 * 10 ^ 24 else if j.val = 2 then 4583319222669465617794 * 487136249780 * 10 ^ 24 else if j.val = 3 then 4583319222669465617794 * 12863749646 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_12 :
    (555850545005742277987116252977 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (12 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (12 : Fin 88) = fun j => if j.val = 0 then 27598267603987961734550 * 336167787 * 10 ^ 24 else if j.val = 1 then 27598267603987961734550 * 79860818860 * 10 ^ 24 else if j.val = 2 then 27598267603987961734550 * 839606064309 * 10 ^ 24 else if j.val = 3 then 27598267603987961734550 * 79860837774 * 10 ^ 24 else if j.val = 4 then 27598267603987961734550 * 336111270 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_13 :
    (769475863036932099238276925251 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (13 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (13 : Fin 88) = fun j => if j.val = 1 then 915717287192554183392 * 7314898303 * 10 ^ 24 else if j.val = 2 then 915717287192554183392 * 492685087925 * 10 ^ 24 else if j.val = 3 then 915717287192554183392 * 492685115133 * 10 ^ 24 else if j.val = 4 then 915717287192554183392 * 7314898639 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_14 :
    (711975965960931129420310727428 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (14 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (14 : Fin 88) = fun j => if j.val = 2 then 110814596949017072568 * 118527640663 * 10 ^ 24 else if j.val = 3 then 110814596949017072568 * 762944722557 * 10 ^ 24 else if j.val = 4 then 110814596949017072568 * 118527636780 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_15 :
    (693147019557438596317210217902 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (15 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (15 : Fin 88) = fun j => if j.val = 0 then 110169238029726659400 * 499716923272 * 10 ^ 24 else if j.val = 1 then 110169238029726659400 * 500283076728 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_16 :
    (693147180559916128578256000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (16 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (16 : Fin 88) = fun j => if j.val = 0 then 553294693951647161070 * 500000085412 * 10 ^ 24 else if j.val = 1 then 553294693951647161070 * 499999914588 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_17 :
    (693147180559781085096716000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (17 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (17 : Fin 88) = fun j => if j.val = 0 then 6852937681615717442160 * 499999797377 * 10 ^ 24 else if j.val = 1 then 6852937681615717442160 * 500000202623 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_18 :
    (693147180559944554596556000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (18 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (18 : Fin 88) = fun j => if j.val = 0 then 3875209754433415815974 * 500000013737 * 10 ^ 24 else if j.val = 1 then 3875209754433415815974 * 499999986263 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_19 :
    (693146929971782060771772680129 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (19 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (19 : Fin 88) = fun j => if j.val = 0 then 109598382243794462278 * 500352687041 * 10 ^ 24 else if j.val = 1 then 109598382243794462278 * 499647312959 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_20 :
    (908324653164129361109114172010 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (20 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (20 : Fin 88) = fun j => if j.val = 0 then 2051847738255341859836 * 182133617006 * 10 ^ 24 else if j.val = 1 then 2051847738255341859836 * 635732855086 * 10 ^ 24 else if j.val = 2 then 2051847738255341859836 * 182133527908 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_21 :
    (904206293819026161576700716900 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (21 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (21 : Fin 88) = fun j => if j.val = 0 then 7869101871661276298088 * 180495559093 * 10 ^ 24 else if j.val = 1 then 7869101871661276298088 * 639008881410 * 10 ^ 24 else if j.val = 2 then 7869101871661276298088 * 180495559497 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_22 :
    (911288457378825506214644489106 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (22 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (22 : Fin 88) = fun j => if j.val = 0 then 34888091120226875815908 * 183323962708 * 10 ^ 24 else if j.val = 1 then 34888091120226875815908 * 633352101157 * 10 ^ 24 else if j.val = 2 then 34888091120226875815908 * 183323936135 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_23 :
    (900555968655753301800179116500 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (23 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (23 : Fin 88) = fun j => if j.val = 0 then 3447291078618988929820 * 179058962292 * 10 ^ 24 else if j.val = 1 then 3447291078618988929820 * 641882140880 * 10 ^ 24 else if j.val = 2 then 3447291078618988929820 * 179058896828 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_24 :
    (811733098362212365480759912249 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (24 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (24 : Fin 88) = fun j => if j.val = 0 then 32291967987013664532806 * 12729745951 * 10 ^ 24 else if j.val = 1 then 32291967987013664532806 * 487270255397 * 10 ^ 24 else if j.val = 2 then 32291967987013664532806 * 487270252843 * 10 ^ 24 else if j.val = 3 then 32291967987013664532806 * 12729745809 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_25 :
    (809344676651586565770823427204 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (25 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (25 : Fin 88) = fun j => if j.val = 0 then 35588977010439180914298 * 12403313313 * 10 ^ 24 else if j.val = 1 then 35588977010439180914298 * 487596688451 * 10 ^ 24 else if j.val = 2 then 35588977010439180914298 * 487596725170 * 10 ^ 24 else if j.val = 3 then 35588977010439180914298 * 12403273066 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_26 :
    (812602944578479446879303050722 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (26 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (26 : Fin 88) = fun j => if j.val = 0 then 36317267733912428022238 * 12849270661 * 10 ^ 24 else if j.val = 1 then 36317267733912428022238 * 487150749892 * 10 ^ 24 else if j.val = 2 then 36317267733912428022238 * 487150781941 * 10 ^ 24 else if j.val = 3 then 36317267733912428022238 * 12849197506 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_27 :
    (809619621532047860129961011977 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (27 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else 0) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (27 : Fin 88) = fun j => if j.val = 0 then 1298656623467343632725 * 12440769554 * 10 ^ 24 else if j.val = 1 then 1298656623467343632725 * 487559219349 * 10 ^ 24 else if j.val = 2 then 1298656623467343632725 * 487559276693 * 10 ^ 24 else if j.val = 3 then 1298656623467343632725 * 12440734404 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_28 :
    (555851252741100416460493037452 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (28 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (28 : Fin 88) = fun j => if j.val = 0 then 28096363841571444039635 * 336085250 * 10 ^ 24 else if j.val = 1 then 28096363841571444039635 * 79861227076 * 10 ^ 24 else if j.val = 2 then 28096363841571444039635 * 839605379151 * 10 ^ 24 else if j.val = 3 then 28096363841571444039635 * 79861279991 * 10 ^ 24 else if j.val = 4 then 28096363841571444039635 * 336028532 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_29 :
    (769492141080313619278948956617 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (29 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (29 : Fin 88) = fun j => if j.val = 1 then 912554197159031363655 * 7318842669 * 10 ^ 24 else if j.val = 2 then 912554197159031363655 * 492685090521 * 10 ^ 24 else if j.val = 3 then 912554197159031363655 * 492681245786 * 10 ^ 24 else if j.val = 4 then 912554197159031363655 * 7314821024 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_30 :
    (711976117674158012225566086244 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (30 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (30 : Fin 88) = fun j => if j.val = 2 then 110808482762711770245 * 118527681409 * 10 ^ 24 else if j.val = 3 then 110808482762711770245 * 762944641077 * 10 ^ 24 else if j.val = 4 then 110808482762711770245 * 118527677514 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_31 :
    (693147180559938773664896000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (31 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (31 : Fin 88) = fun j => if j.val = 0 then 109696435330058679800 * 500000040422 * 10 ^ 24 else if j.val = 1 then 109696435330058679800 * 499999959578 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_32 :
    (693147180559868793005776000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (32 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (32 : Fin 88) = fun j => if j.val = 0 then 10523423710807000306144 * 499999861692 * 10 ^ 24 else if j.val = 1 then 10523423710807000306144 * 500000138308 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_33 :
    (693147180559945202004736000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (33 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (33 : Fin 88) = fun j => if j.val = 0 then 3237129756997996772000 * 499999994818 * 10 ^ 24 else if j.val = 1 then 3237129756997996772000 * 500000005182 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_34 :
    (693147177046391943662476000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (34 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (34 : Fin 88) = fun j => if j.val = 0 then 111371972178627657280 * 499970362383 * 10 ^ 24 else if j.val = 1 then 111371972178627657280 * 500029637617 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_35 :
    (900222716433259543262016590802 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (35 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (35 : Fin 88) = fun j => if j.val = 0 then 2337548271600266664368 * 178928496130 * 10 ^ 24 else if j.val = 1 then 2337548271600266664368 * 642143053642 * 10 ^ 24 else if j.val = 2 then 2337548271600266664368 * 178928450228 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_36 :
    (904205308235660137585363744138 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (36 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (36 : Fin 88) = fun j => if j.val = 0 then 774507148045033287717 * 180495168569 * 10 ^ 24 else if j.val = 1 then 774507148045033287717 * 639009661031 * 10 ^ 24 else if j.val = 2 then 774507148045033287717 * 180495170400 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_37 :
    (913528871650788878400849912786 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (37 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (37 : Fin 88) = fun j => if j.val = 0 then 2831677960029220116958 * 184230634355 * 10 ^ 24 else if j.val = 1 then 2831677960029220116958 * 631539280433 * 10 ^ 24 else if j.val = 2 then 2831677960029220116958 * 184230085212 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_38 :
    (809598983811209326628196309628 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (38 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else -6) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (38 : Fin 88) = fun j => if j.val = 0 then 38948654436342761089250 * 12437942368 * 10 ^ 24 else if j.val = 1 then 38948654436342761089250 * 487562053251 * 10 ^ 24 else if j.val = 2 then 38948654436342761089250 * 487562068259 * 10 ^ 24 else if j.val = 3 then 38948654436342761089250 * 12437936122 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_39 :
    (808502794610303472878371004261 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (39 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (39 : Fin 88) = fun j => if j.val = 0 then 35562042575249745026250 * 12288807308 * 10 ^ 24 else if j.val = 1 then 35562042575249745026250 * 487711193521 * 10 ^ 24 else if j.val = 2 then 35562042575249745026250 * 487711224530 * 10 ^ 24 else if j.val = 3 then 35562042575249745026250 * 12288774641 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_40 :
    (811881146182707807227824562860 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (40 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (40 : Fin 88) = fun j => if j.val = 0 then 25781021993817692799460 * 12750113010 * 10 ^ 24 else if j.val = 1 then 25781021993817692799460 * 487249908078 * 10 ^ 24 else if j.val = 2 then 25781021993817692799460 * 487249971971 * 10 ^ 24 else if j.val = 3 then 25781021993817692799460 * 12750006941 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_41 :
    (814039185848595216013633377458 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (41 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (41 : Fin 88) = fun j => if j.val = 0 then 5887082376587153617382 * 13047222153 * 10 ^ 24 else if j.val = 1 then 5887082376587153617382 * 486952769964 * 10 ^ 24 else if j.val = 2 then 5887082376587153617382 * 486952835306 * 10 ^ 24 else if j.val = 3 then 5887082376587153617382 * 13047172577 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_42 :
    (541182247017802746302147489224 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (42 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 2) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (42 : Fin 88) = fun j => if j.val = 0 then 18561628792168432026484 * 328573013 * 10 ^ 24 else if j.val = 1 then 18561628792168432026484 * 76798748343 * 10 ^ 24 else if j.val = 2 then 18561628792168432026484 * 845745354678 * 10 ^ 24 else if j.val = 3 then 18561628792168432026484 * 76798829288 * 10 ^ 24 else if j.val = 4 then 18561628792168432026484 * 328494678 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_1_43 :
    (768104296163267922106359969004 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (43 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 1) 0 (43 : Fin 88) = fun j => if j.val = 1 then 469860220723925525436 * 7152438602 * 10 ^ 24 else if j.val = 2 then 469860220723925525436 * 492847545515 * 10 ^ 24 else if j.val = 3 then 469860220723925525436 * 492847573098 * 10 ^ 24 else if j.val = 4 then 469860220723925525436 * 7152442785 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((693147180559618866309328000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (0 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559799692383628000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (1 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559936673804048000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (2 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147145124760630225168398787 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (3 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900151104605742571664134942889 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (4 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((903985168998886939806454299319 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (5 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else if j.val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911405122907626736707021348512 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (6 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908860533067974456378748142475 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (7 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 6) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((810274913600030122887928943948 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (8 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809309904486167137701404409219 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (9 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else -4) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812635644499153393521685415167 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (10 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812708501880274337221076000953 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (11 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((555850545005742277987116252977 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (12 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((769475863036932099238276925251 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (13 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((711975965960931129420310727428 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (14 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147019557438596317210217902 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (15 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559916128578256000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (16 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559781085096716000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (17 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559944554596556000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (18 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693146929971782060771772680129 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (19 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908324653164129361109114172010 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (20 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904206293819026161576700716900 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (21 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911288457378825506214644489106 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (22 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900555968655753301800179116500 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (23 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811733098362212365480759912249 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (24 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809344676651586565770823427204 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (25 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812602944578479446879303050722 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (26 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809619621532047860129961011977 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (27 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else 0) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((555851252741100416460493037452 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (28 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((769492141080313619278948956617 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (29 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((711976117674158012225566086244 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (30 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559938773664896000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (31 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559868793005776000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (32 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945202004736000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (33 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147177046391943662476000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (34 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900222716433259543262016590802 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (35 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904205308235660137585363744138 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (36 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913528871650788878400849912786 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (37 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809598983811209326628196309628 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (38 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else -6) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808502794610303472878371004261 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (39 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811881146182707807227824562860 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (40 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((814039185848595216013633377458 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (41 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((541182247017802746302147489224 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (42 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 2) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((768104296163267922106359969004 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 1) 0 (43 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.cr_1_0, L3C.cr_1_1, L3C.cr_1_2, L3C.cr_1_3, L3C.cr_1_4, L3C.cr_1_5, L3C.cr_1_6, L3C.cr_1_7, L3C.cr_1_8, L3C.cr_1_9, L3C.cr_1_10, L3C.cr_1_11, L3C.cr_1_12, L3C.cr_1_13, L3C.cr_1_14, L3C.cr_1_15, L3C.cr_1_16, L3C.cr_1_17, L3C.cr_1_18, L3C.cr_1_19, L3C.cr_1_20, L3C.cr_1_21, L3C.cr_1_22, L3C.cr_1_23, L3C.cr_1_24, L3C.cr_1_25, L3C.cr_1_26, L3C.cr_1_27, L3C.cr_1_28, L3C.cr_1_29, L3C.cr_1_30, L3C.cr_1_31, L3C.cr_1_32, L3C.cr_1_33, L3C.cr_1_34, L3C.cr_1_35, L3C.cr_1_36, L3C.cr_1_37, L3C.cr_1_38, L3C.cr_1_39, L3C.cr_1_40, L3C.cr_1_41, L3C.cr_1_42, L3C.cr_1_43⟩
