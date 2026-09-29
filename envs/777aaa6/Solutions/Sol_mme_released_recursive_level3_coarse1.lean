-- Prove2me | solution 1 for mme_released_recursive_level3_coarse1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:09:32.102211+00:00
-- url     : https://prove2.me/submissions/6b011852-272b-4da1-8b40-6558c353dea1

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

theorem cr_0_23 :
    (900143281684103741935297179379 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (23 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (23 : Fin 88) = fun j => if j.val = 0 then 2338402430621028675848 * 178897417829 * 10 ^ 24 else if j.val = 1 then 2338402430621028675848 * 642205209439 * 10 ^ 24 else if j.val = 2 then 2338402430621028675848 * 178897372732 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_24 :
    (812706612645017064015083489772 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (24 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (24 : Fin 88) = fun j => if j.val = 0 then 4668877469698821833048 * 12863502037 * 10 ^ 24 else if j.val = 1 then 4668877469698821833048 * 487136494398 * 10 ^ 24 else if j.val = 2 then 4668877469698821833048 * 487136514268 * 10 ^ 24 else if j.val = 3 then 4668877469698821833048 * 12863489297 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_25 :
    (812619737579763544362967928339 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (25 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (25 : Fin 88) = fun j => if j.val = 0 then 33270232565701371597524 * 12851556744 * 10 ^ 24 else if j.val = 1 then 33270232565701371597524 * 487148443324 * 10 ^ 24 else if j.val = 2 then 33270232565701371597524 * 487148468547 * 10 ^ 24 else if j.val = 3 then 33270232565701371597524 * 12851531385 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_26 :
    (809265226404075963387786724975 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (26 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (26 : Fin 88) = fun j => if j.val = 0 then 37848003636402927281490 * 12392503877 * 10 ^ 24 else if j.val = 1 then 37848003636402927281490 * 487607512028 * 10 ^ 24 else if j.val = 2 then 37848003636402927281490 * 487607538727 * 10 ^ 24 else if j.val = 3 then 37848003636402927281490 * 12392445368 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_27 :
    (810272817366879618724364025342 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (27 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (27 : Fin 88) = fun j => if j.val = 0 then 37992807395602638462230 * 12529875750 * 10 ^ 24 else if j.val = 1 then 37992807395602638462230 * 487470121296 * 10 ^ 24 else if j.val = 2 then 37992807395602638462230 * 487470138014 * 10 ^ 24 else if j.val = 3 then 37992807395602638462230 * 12529864940 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_28 :
    (555854434454634159370925652310 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (28 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (28 : Fin 88) = fun j => if j.val = 0 then 27993824086544358005983 * 336160439 * 10 ^ 24 else if j.val = 1 then 27993824086544358005983 * 79861676318 * 10 ^ 24 else if j.val = 2 then 27993824086544358005983 * 839604329175 * 10 ^ 24 else if j.val = 3 then 27993824086544358005983 * 79861750656 * 10 ^ 24 else if j.val = 4 then 27993824086544358005983 * 336083412 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_29 :
    (769467640694981510114992996746 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (29 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else -1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (29 : Fin 88) = fun j => if j.val = 1 then 953174036668402816574 * 7313923380 * 10 ^ 24 else if j.val = 2 then 953174036668402816574 * 492686069205 * 10 ^ 24 else if j.val = 3 then 953174036668402816574 * 492686086859 * 10 ^ 24 else if j.val = 4 then 953174036668402816574 * 7313920556 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_30 :
    (711896058627967083758254535474 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (30 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (30 : Fin 88) = fun j => if j.val = 2 then 110808742479067029870 * 118510479542 * 10 ^ 24 else if j.val = 3 then 110808742479067029870 * 762987632946 * 10 ^ 24 else if j.val = 4 then 110808742479067029870 * 118501887512 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_31 :
    (693147180559650970616332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (31 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (31 : Fin 88) = fun j => if j.val = 0 then 109633903025058746440 * 500000271265 * 10 ^ 24 else if j.val = 1 then 109633903025058746440 * 499999728735 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_32 :
    (693147180559945306520428000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (32 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (32 : Fin 88) = fun j => if j.val = 0 then 3852690397987601220578 * 499999999149 * 10 ^ 24 else if j.val = 1 then 3852690397987601220578 * 500000000851 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_33 :
    (693147180559939773759628000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (33 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (33 : Fin 88) = fun j => if j.val = 0 then 7148580403613912966538 * 500000037201 * 10 ^ 24 else if j.val = 1 then 7148580403613912966538 * 499999962799 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_34 :
    (693147180559932520521488000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (34 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (34 : Fin 88) = fun j => if j.val = 0 then 1015726222663453773600 * 500000056544 * 10 ^ 24 else if j.val = 1 then 1015726222663453773600 * 499999943456 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_35 :
    (693147180373815825004048000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (35 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (35 : Fin 88) = fun j => if j.val = 0 then 110855808232269478315 * 500006821464 * 10 ^ 24 else if j.val = 1 then 110855808232269478315 * 499993178536 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_36 :
    (900628665580315766929266797713 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (36 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (36 : Fin 88) = fun j => if j.val = 0 then 3459853758069617270648 * 179087450004 * 10 ^ 24 else if j.val = 1 then 3459853758069617270648 * 641825193320 * 10 ^ 24 else if j.val = 2 then 3459853758069617270648 * 179087356676 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_37 :
    (911349132061385003361554116252 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (37 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (37 : Fin 88) = fun j => if j.val = 0 then 35261338173587647107896 * 183348418226 * 10 ^ 24 else if j.val = 1 then 35261338173587647107896 * 633303158562 * 10 ^ 24 else if j.val = 2 then 35261338173587647107896 * 183348423212 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_38 :
    (904427131354296295448399588481 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (38 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (38 : Fin 88) = fun j => if j.val = 0 then 8085195559745806413744 * 180582932619 * 10 ^ 24 else if j.val = 1 then 8085195559745806413744 * 638834143477 * 10 ^ 24 else if j.val = 2 then 8085195559745806413744 * 180582923904 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_39 :
    (911281491506505390544343957706 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (39 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (39 : Fin 88) = fun j => if j.val = 0 then 1778448524590342322432 * 183321221364 * 10 ^ 24 else if j.val = 1 then 1778448524590342322432 * 633357719040 * 10 ^ 24 else if j.val = 2 then 1778448524590342322432 * 183321059596 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_40 :
    (809118194603984395335597695869 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (40 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (40 : Fin 88) = fun j => if j.val = 0 then 789541275298315861382 * 12372473959 * 10 ^ 24 else if j.val = 1 then 789541275298315861382 * 487627518094 * 10 ^ 24 else if j.val = 2 then 789541275298315861382 * 487627560380 * 10 ^ 24 else if j.val = 3 then 789541275298315861382 * 12372447567 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_41 :
    (811794464518464740581171904405 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (41 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (41 : Fin 88) = fun j => if j.val = 0 then 32575434626639900246874 * 12738168596 * 10 ^ 24 else if j.val = 1 then 32575434626639900246874 * 487261826663 * 10 ^ 24 else if j.val = 2 then 32575434626639900246874 * 487261843371 * 10 ^ 24 else if j.val = 3 then 32575434626639900246874 * 12738161370 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_42 :
    (808694830491075194687653057301 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (42 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -2) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (42 : Fin 88) = fun j => if j.val = 0 then 30248270286076841486316 * 12314919949 * 10 ^ 24 else if j.val = 1 then 30248270286076841486316 * 487685089873 * 10 ^ 24 else if j.val = 2 then 30248270286076841486316 * 487685143377 * 10 ^ 24 else if j.val = 3 then 30248270286076841486316 * 12314846801 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_43 :
    (812093434539130765117514227374 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (43 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (43 : Fin 88) = fun j => if j.val = 0 then 29985244508481836465294 * 12779210954 * 10 ^ 24 else if j.val = 1 then 29985244508481836465294 * 487220787108 * 10 ^ 24 else if j.val = 2 then 29985244508481836465294 * 487220802810 * 10 ^ 24 else if j.val = 3 then 29985244508481836465294 * 12779199128 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_44 :
    (541183994604786622867358920394 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (44 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 2) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (44 : Fin 88) = fun j => if j.val = 0 then 18730621411182165786176 * 328577079 * 10 ^ 24 else if j.val = 1 then 18730621411182165786176 * 76799098512 * 10 ^ 24 else if j.val = 2 then 18730621411182165786176 * 845744645398 * 10 ^ 24 else if j.val = 3 then 18730621411182165786176 * 76799179963 * 10 ^ 24 else if j.val = 4 then 18730621411182165786176 * 328499048 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_45 :
    (768129296695063727359260047081 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (45 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (45 : Fin 88) = fun j => if j.val = 1 then 421026630513031172603 * 7155405823 * 10 ^ 24 else if j.val = 2 then 421026630513031172603 * 492844612843 * 10 ^ 24 else if j.val = 3 then 421026630513031172603 * 492844599040 * 10 ^ 24 else if j.val = 4 then 421026630513031172603 * 7155382294 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_46 :
    (705546273754807564419467084968 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (46 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -6) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -1) else if j.val = 4 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (46 : Fin 88) = fun j => if j.val = 2 then 110253718633845970660 * 116809930950 * 10 ^ 24 else if j.val = 3 then 110253718633845970660 * 766380177821 * 10 ^ 24 else if j.val = 4 then 110253718633845970660 * 116809891229 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_47 :
    (693147180538304503144208000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (47 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (47 : Fin 88) = fun j => if j.val = 0 then 110646349088841100955 * 500002325984 * 10 ^ 24 else if j.val = 1 then 110646349088841100955 * 499997674016 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_48 :
    (693147180559943596119568000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (48 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (48 : Fin 88) = fun j => if j.val = 0 then 3561224852440773057436 * 499999979304 * 10 ^ 24 else if j.val = 1 then 3561224852440773057436 * 500000020696 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_49 :
    (693147180559944229111808000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (49 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (49 : Fin 88) = fun j => if j.val = 0 then 9141916713819334125520 * 500000016434 * 10 ^ 24 else if j.val = 1 then 9141916713819334125520 * 499999983566 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_50 :
    (693147180559932184965388000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (50 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (50 : Fin 88) = fun j => if j.val = 0 then 1020688066294425858911 * 500000057281 * 10 ^ 24 else if j.val = 1 then 1020688066294425858911 * 499999942719 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_51 :
    (693147180381900640434988000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (51 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (51 : Fin 88) = fun j => if j.val = 0 then 110872674856248142540 * 500006671669 * 10 ^ 24 else if j.val = 1 then 110872674856248142540 * 499993328331 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_52 :
    (909018675962937370541545888299 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (52 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 3) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (52 : Fin 88) = fun j => if j.val = 0 then 3190272719450719236191 * 182410850907 * 10 ^ 24 else if j.val = 1 then 3190272719450719236191 * 635177120722 * 10 ^ 24 else if j.val = 2 then 3190272719450719236191 * 182412028371 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_53 :
    (911572080208014257678585547337 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (53 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (53 : Fin 88) = fun j => if j.val = 0 then 10616090467421600222432 * 183438370382 * 10 ^ 24 else if j.val = 1 then 10616090467421600222432 * 633123240945 * 10 ^ 24 else if j.val = 2 then 10616090467421600222432 * 183438388673 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_54 :
    (904545515529794066092388100715 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (54 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 2) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (54 : Fin 88) = fun j => if j.val = 0 then 8127611271510001136598 * 180629780238 * 10 ^ 24 else if j.val = 1 then 8127611271510001136598 * 638740431413 * 10 ^ 24 else if j.val = 2 then 8127611271510001136598 * 180629788349 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_55 :
    (911390881298084554412658570906 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (55 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (55 : Fin 88) = fun j => if j.val = 0 then 1780804576694274160481 * 183365334041 * 10 ^ 24 else if j.val = 1 then 1780804576694274160481 * 633269474742 * 10 ^ 24 else if j.val = 2 then 1780804576694274160481 * 183365191217 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_56 :
    (811863572810883420035569230041 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (56 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (56 : Fin 88) = fun j => if j.val = 0 then 4273642688720194215951 * 12747657807 * 10 ^ 24 else if j.val = 1 then 4273642688720194215951 * 487252334905 * 10 ^ 24 else if j.val = 2 then 4273642688720194215951 * 487252368704 * 10 ^ 24 else if j.val = 3 then 4273642688720194215951 * 12747638584 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_57 :
    (811300120261335144305300179639 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (57 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (57 : Fin 88) = fun j => if j.val = 0 then 26234019409813223425551 * 12670397855 * 10 ^ 24 else if j.val = 1 then 26234019409813223425551 * 487329600251 * 10 ^ 24 else if j.val = 2 then 26234019409813223425551 * 487329621345 * 10 ^ 24 else if j.val = 3 then 26234019409813223425551 * 12670380549 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_58 :
    (808205215023607930219899573387 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (58 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (58 : Fin 88) = fun j => if j.val = 0 then 28069108486075679996000 * 12248430087 * 10 ^ 24 else if j.val = 1 then 28069108486075679996000 * 487751586097 * 10 ^ 24 else if j.val = 2 then 28069108486075679996000 * 487751635927 * 10 ^ 24 else if j.val = 3 then 28069108486075679996000 * 12248347889 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_59 :
    (811593908518543004741843400323 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (59 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (59 : Fin 88) = fun j => if j.val = 0 then 30355291583649730909196 * 12710663623 * 10 ^ 24 else if j.val = 1 then 30355291583649730909196 * 487289334298 * 10 ^ 24 else if j.val = 2 then 30355291583649730909196 * 487289354207 * 10 ^ 24 else if j.val = 3 then 30355291583649730909196 * 12710647872 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_60 :
    (695811142749872007098311112911 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (60 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -5) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (60 : Fin 88) = fun j => if j.val = 2 then 109686396664275155878 * 114237887929 * 10 ^ 24 else if j.val = 3 then 109686396664275155878 * 771515967401 * 10 ^ 24 else if j.val = 4 then 109686396664275155878 * 114246144670 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_61 :
    (693147171639299387253617349348 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (61 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -3) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (61 : Fin 88) = fun j => if j.val = 0 then 111367256841534290010 * 499948359345 * 10 ^ 24 else if j.val = 1 then 111367256841534290010 * 500051640655 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_62 :
    (693147180559945250526956000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (62 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (62 : Fin 88) = fun j => if j.val = 0 then 3200020600325682870540 * 499999996163 * 10 ^ 24 else if j.val = 1 then 3200020600325682870540 * 500000003837 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_63 :
    (693147180559942589794732000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (63 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (63 : Fin 88) = fun j => if j.val = 0 then 10614889161665752679443 * 500000026075 * 10 ^ 24 else if j.val = 1 then 10614889161665752679443 * 499999973925 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_64 :
    (693146883612921187278877001735 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (64 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (64 : Fin 88) = fun j => if j.val = 0 then 109632826179711249051 * 500383937421 * 10 ^ 24 else if j.val = 1 then 109632826179711249051 * 499616062579 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_65 :
    (913526591817096872941452372116 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (65 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (65 : Fin 88) = fun j => if j.val = 0 then 2802759484678642772007 * 184229476961 * 10 ^ 24 else if j.val = 1 then 2802759484678642772007 * 631541130950 * 10 ^ 24 else if j.val = 2 then 2802759484678642772007 * 184229392089 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_0_66 :
    (904124171690608764942498365949 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (66 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 0) 0 (66 : Fin 88) = fun j => if j.val = 0 then 1184415063497108503930 * 180463079202 * 10 ^ 24 else if j.val = 1 then 1184415063497108503930 * 639073829625 * 10 ^ 24 else if j.val = 2 then 1184415063497108503930 * 180463091173 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((900143281684103741935297179379 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (23 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812706612645017064015083489772 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (24 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812619737579763544362967928339 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (25 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809265226404075963387786724975 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (26 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((810272817366879618724364025342 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (27 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((555854434454634159370925652310 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (28 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((769467640694981510114992996746 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (29 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else -1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((711896058627967083758254535474 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (30 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559650970616332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (31 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945306520428000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (32 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559939773759628000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (33 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559932520521488000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (34 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180373815825004048000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (35 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900628665580315766929266797713 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (36 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911349132061385003361554116252 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (37 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904427131354296295448399588481 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (38 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911281491506505390544343957706 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (39 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809118194603984395335597695869 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (40 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811794464518464740581171904405 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (41 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808694830491075194687653057301 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (42 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -2) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812093434539130765117514227374 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (43 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((541183994604786622867358920394 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (44 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 2) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((768129296695063727359260047081 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (45 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((705546273754807564419467084968 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (46 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -6) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -1) else if j.val = 4 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180538304503144208000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (47 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943596119568000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (48 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559944229111808000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (49 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559932184965388000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (50 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180381900640434988000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (51 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((909018675962937370541545888299 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (52 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 3) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911572080208014257678585547337 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (53 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904545515529794066092388100715 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (54 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 2) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911390881298084554412658570906 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (55 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811863572810883420035569230041 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (56 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811300120261335144305300179639 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (57 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808205215023607930219899573387 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (58 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811593908518543004741843400323 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (59 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((695811142749872007098311112911 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (60 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -5) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147171639299387253617349348 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (61 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -3) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945250526956000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (62 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559942589794732000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (63 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693146883612921187278877001735 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (64 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913526591817096872941452372116 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (65 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904124171690608764942498365949 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (66 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.cr_0_23, L3C.cr_0_24, L3C.cr_0_25, L3C.cr_0_26, L3C.cr_0_27, L3C.cr_0_28, L3C.cr_0_29, L3C.cr_0_30, L3C.cr_0_31, L3C.cr_0_32, L3C.cr_0_33, L3C.cr_0_34, L3C.cr_0_35, L3C.cr_0_36, L3C.cr_0_37, L3C.cr_0_38, L3C.cr_0_39, L3C.cr_0_40, L3C.cr_0_41, L3C.cr_0_42, L3C.cr_0_43, L3C.cr_0_44, L3C.cr_0_45, L3C.cr_0_46, L3C.cr_0_47, L3C.cr_0_48, L3C.cr_0_49, L3C.cr_0_50, L3C.cr_0_51, L3C.cr_0_52, L3C.cr_0_53, L3C.cr_0_54, L3C.cr_0_55, L3C.cr_0_56, L3C.cr_0_57, L3C.cr_0_58, L3C.cr_0_59, L3C.cr_0_60, L3C.cr_0_61, L3C.cr_0_62, L3C.cr_0_63, L3C.cr_0_64, L3C.cr_0_65, L3C.cr_0_66⟩
