-- Prove2me | solution 1 for mme_released_recursive_level3_coarse2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:09:32.272552+00:00
-- url     : https://prove2.me/submissions/9039f44f-b1d7-4769-9c51-e3a3e7c39aaa

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

theorem cr_0_67 :
    (900212286091271437980552632743 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (67 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else -3) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (67 : Fin 88) = fun j => if j.val = 0 then 2341315562025556471236 * 178924455466 * 10 ^ 24 else if j.val = 1 then 2341315562025556471236 * 642151215952 * 10 ^ 24 else if j.val = 2 then 2341315562025556471236 * 178924328582 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_68 :
    (814020997571556262646186274152 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (68 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (68 : Fin 88) = fun j => if j.val = 0 then 6044901480888335032132 * 13044688311 * 10 ^ 24 else if j.val = 1 then 6044901480888335032132 * 486955311176 * 10 ^ 24 else if j.val = 2 then 6044901480888335032132 * 486955318907 * 10 ^ 24 else if j.val = 3 then 6044901480888335032132 * 13044681606 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_69 :
    (811872885977731439162263465055 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (69 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (69 : Fin 88) = fun j => if j.val = 0 then 25742696099525811314930 * 12748935650 * 10 ^ 24 else if j.val = 1 then 25742696099525811314930 * 487251066199 * 10 ^ 24 else if j.val = 2 then 25742696099525811314930 * 487251081155 * 10 ^ 24 else if j.val = 3 then 25742696099525811314930 * 12748916996 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_70 :
    (808499677986548161859566118168 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (70 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (70 : Fin 88) = fun j => if j.val = 0 then 35305197000849047245590 * 12288397369 * 10 ^ 24 else if j.val = 1 then 35305197000849047245590 * 487711616801 * 10 ^ 24 else if j.val = 2 then 35305197000849047245590 * 487711647919 * 10 ^ 24 else if j.val = 3 then 35305197000849047245590 * 12288337911 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_71 :
    (809558546240310416130717287693 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (71 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else 0) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (71 : Fin 88) = fun j => if j.val = 0 then 38455102061686906176449 * 12432435737 * 10 ^ 24 else if j.val = 1 then 38455102061686906176449 * 487567558601 * 10 ^ 24 else if j.val = 2 then 38455102061686906176449 * 487567584423 * 10 ^ 24 else if j.val = 3 then 38455102061686906176449 * 12432421239 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_72 :
    (541190163305253896507708744179 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (72 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (72 : Fin 88) = fun j => if j.val = 0 then 18193280658643192595892 * 328678745 * 10 ^ 24 else if j.val = 1 then 18193280658643192595892 * 76800048281 * 10 ^ 24 else if j.val = 2 then 18193280658643192595892 * 845742536248 * 10 ^ 24 else if j.val = 3 then 18193280658643192595892 * 76800136038 * 10 ^ 24 else if j.val = 4 then 18193280658643192595892 * 328600688 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_73 :
    (768130699273850125863518832468 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (73 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (73 : Fin 88) = fun j => if j.val = 1 then 405929511182391566920 * 7155556365 * 10 ^ 24 else if j.val = 2 then 405929511182391566920 * 492844371431 * 10 ^ 24 else if j.val = 3 then 405929511182391566920 * 492844509056 * 10 ^ 24 else if j.val = 4 then 405929511182391566920 * 7155563148 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_74 :
    (705541177832590360516657868146 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (74 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (74 : Fin 88) = fun j => if j.val = 2 then 110242411831095174528 * 116808558365 * 10 ^ 24 else if j.val = 3 then 110242411831095174528 * 766382886819 * 10 ^ 24 else if j.val = 4 then 110242411831095174528 * 116808554816 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_75 :
    (693147171639624124828193384455 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (75 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -3) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (75 : Fin 88) = fun j => if j.val = 0 then 111445382014040884224 * 499948368092 * 10 ^ 24 else if j.val = 1 then 111445382014040884224 * 500051631908 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_76 :
    (693147180559945244775632000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (76 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (76 : Fin 88) = fun j => if j.val = 0 then 3199352595399596276383 * 499999995980 * 10 ^ 24 else if j.val = 1 then 3199352595399596276383 * 500000004020 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_77 :
    (693147180559943702690176000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (77 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (77 : Fin 88) = fun j => if j.val = 0 then 10757103157606973235969 * 500000020042 * 10 ^ 24 else if j.val = 1 then 10757103157606973235969 * 499999979958 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_78 :
    (693147180559932815543056000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (78 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (78 : Fin 88) = fun j => if j.val = 0 then 547314933383461180152 * 499999944112 * 10 ^ 24 else if j.val = 1 then 547314933383461180152 * 500000055888 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_79 :
    (693147120625953775262846680456 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (79 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (79 : Fin 88) = fun j => if j.val = 0 then 110281620997937638620 * 500168466990 * 10 ^ 24 else if j.val = 1 then 110281620997937638620 * 499831533010 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_80 :
    (913647122748691780373737902752 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (80 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (80 : Fin 88) = fun j => if j.val = 0 then 2844274767837393260500 * 184278358956 * 10 ^ 24 else if j.val = 1 then 2844274767837393260500 * 631443278044 * 10 ^ 24 else if j.val = 2 then 2844274767837393260500 * 184278363000 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_81 :
    (904446127607146579504889154834 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (81 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (81 : Fin 88) = fun j => if j.val = 0 then 7042066099602865294704 * 180590395735 * 10 ^ 24 else if j.val = 1 then 7042066099602865294704 * 638819108046 * 10 ^ 24 else if j.val = 2 then 7042066099602865294704 * 180590496219 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_82 :
    (908483299955031022045957411993 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (82 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (82 : Fin 88) = fun j => if j.val = 0 then 2072668777206426302096 * 182197053384 * 10 ^ 24 else if j.val = 1 then 2072668777206426302096 * 635605913748 * 10 ^ 24 else if j.val = 2 then 2072668777206426302096 * 182197032868 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_83 :
    (813659824156934954085343402929 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (83 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (83 : Fin 88) = fun j => if j.val = 0 then 5943998956570462546744 * 12994837740 * 10 ^ 24 else if j.val = 1 then 5943998956570462546744 * 487005155850 * 10 ^ 24 else if j.val = 2 then 5943998956570462546744 * 487005196976 * 10 ^ 24 else if j.val = 3 then 5943998956570462546744 * 12994809434 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_84 :
    (811366612583904607901922748229 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (84 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (84 : Fin 88) = fun j => if j.val = 0 then 22620795235393111106080 * 12679514217 * 10 ^ 24 else if j.val = 1 then 22620795235393111106080 * 487320488166 * 10 ^ 24 else if j.val = 2 then 22620795235393111106080 * 487320512992 * 10 ^ 24 else if j.val = 3 then 22620795235393111106080 * 12679484625 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_85 :
    (808097864634233751147904727478 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (85 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (85 : Fin 88) = fun j => if j.val = 0 then 30605083537277768597728 * 12233860822 * 10 ^ 24 else if j.val = 1 then 30605083537277768597728 * 487766154350 * 10 ^ 24 else if j.val = 2 then 30605083537277768597728 * 487766198770 * 10 ^ 24 else if j.val = 3 then 30605083537277768597728 * 12233786058 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_86 :
    (810507477908675725362008831130 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (86 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (86 : Fin 88) = fun j => if j.val = 0 then 32938786922516743302419 * 12561929793 * 10 ^ 24 else if j.val = 1 then 32938786922516743302419 * 487438074570 * 10 ^ 24 else if j.val = 2 then 32938786922516743302419 * 487438066873 * 10 ^ 24 else if j.val = 3 then 32938786922516743302419 * 12561928764 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_87 :
    (695750848578236785320619975040 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (87 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (87 : Fin 88) = fun j => if j.val = 2 then 109625649474791310308 * 114269291822 * 10 ^ 24 else if j.val = 3 then 109625649474791310308 * 771547525548 * 10 ^ 24 else if j.val = 4 then 109625649474791310308 * 114183182630 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((900212286091271437980552632743 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (67 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else -3) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((814020997571556262646186274152 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (68 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811872885977731439162263465055 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (69 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808499677986548161859566118168 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (70 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809558546240310416130717287693 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (71 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else 0) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((541190163305253896507708744179 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (72 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((768130699273850125863518832468 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (73 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((705541177832590360516657868146 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (74 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147171639624124828193384455 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (75 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -3) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945244775632000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (76 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943702690176000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (77 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559932815543056000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (78 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147120625953775262846680456 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (79 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913647122748691780373737902752 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (80 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904446127607146579504889154834 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (81 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908483299955031022045957411993 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (82 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((813659824156934954085343402929 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (83 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811366612583904607901922748229 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (84 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808097864634233751147904727478 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (85 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((810507477908675725362008831130 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (86 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((695750848578236785320619975040 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (87 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.cr_0_67, L3C.cr_0_68, L3C.cr_0_69, L3C.cr_0_70, L3C.cr_0_71, L3C.cr_0_72, L3C.cr_0_73, L3C.cr_0_74, L3C.cr_0_75, L3C.cr_0_76, L3C.cr_0_77, L3C.cr_0_78, L3C.cr_0_79, L3C.cr_0_80, L3C.cr_0_81, L3C.cr_0_82, L3C.cr_0_83, L3C.cr_0_84, L3C.cr_0_85, L3C.cr_0_86, L3C.cr_0_87⟩
