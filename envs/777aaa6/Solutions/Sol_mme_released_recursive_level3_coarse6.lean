-- Prove2me | solution 1 for mme_released_recursive_level3_coarse6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T10:24:07.749228+00:00
-- url     : https://prove2.me/submissions/453f9775-438f-44e3-9f2f-8d2aec74c762

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

theorem cr_2_44 :
    (908325359119530596334407931475 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (44 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (44 : Fin 88) = fun j => if j.val = 0 then 2047683600843706309806 * 182133868536 * 10 ^ 24 else if j.val = 1 then 2047683600843706309806 * 635732290333 * 10 ^ 24 else if j.val = 2 then 2047683600843706309806 * 182133841131 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_45 :
    (693147180559943273061356000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (45 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (45 : Fin 88) = fun j => if j.val = 0 then 110216540174478019604 * 499999977437 * 10 ^ 24 else if j.val = 1 then 110216540174478019604 * 500000022563 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_46 :
    (693147155156113274603046306473 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (46 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (46 : Fin 88) = fun j => if j.val = 0 then 110541610394793142487 * 499887308688 * 10 ^ 24 else if j.val = 1 then 110541610394793142487 * 500112691312 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_47 :
    (908832442499560987486825367967 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (47 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 6) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (47 : Fin 88) = fun j => if j.val = 0 then 3158873760010093011788 * 182336833428 * 10 ^ 24 else if j.val = 1 then 3158873760010093011788 * 635326350967 * 10 ^ 24 else if j.val = 2 then 3158873760010093011788 * 182336815605 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_48 :
    (812705119321585476734271786928 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (48 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (48 : Fin 88) = fun j => if j.val = 0 then 4387867945939366084525 * 12863318511 * 10 ^ 24 else if j.val = 1 then 4387867945939366084525 * 487136672123 * 10 ^ 24 else if j.val = 2 then 4387867945939366084525 * 487136747414 * 10 ^ 24 else if j.val = 3 then 4387867945939366084525 * 12863261952 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_49 :
    (769499735418699768720615863817 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (49 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (49 : Fin 88) = fun j => if j.val = 1 then 902095366513904370935 * 7317715506 * 10 ^ 24 else if j.val = 2 then 902095366513904370935 * 492682312445 * 10 ^ 24 else if j.val = 3 then 902095366513904370935 * 492682219981 * 10 ^ 24 else if j.val = 4 then 902095366513904370935 * 7317752068 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_50 :
    (712145688982461635277570329004 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (50 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (36 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (50 : Fin 88) = fun j => if j.val = 2 then 110803976065474319230 * 118557575912 * 10 ^ 24 else if j.val = 3 then 110803976065474319230 * 762853559032 * 10 ^ 24 else if j.val = 4 then 110803976065474319230 * 118588865056 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_51 :
    (693147180559945056797996000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (51 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (51 : Fin 88) = fun j => if j.val = 0 then 3597717083863414277051 * 500000007947 * 10 ^ 24 else if j.val = 1 then 3597717083863414277051 * 499999992053 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_52 :
    (911389002611906535961335434213 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (52 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (52 : Fin 88) = fun j => if j.val = 0 then 10365072552239755133655 * 183364510613 * 10 ^ 24 else if j.val = 1 then 10365072552239755133655 * 633270990498 * 10 ^ 24 else if j.val = 2 then 10365072552239755133655 * 183364498889 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_53 :
    (812610097014610981038876394507 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (53 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (53 : Fin 88) = fun j => if j.val = 0 then 33449169484642678123384 * 12849937155 * 10 ^ 24 else if j.val = 1 then 33449169484642678123384 * 487149965284 * 10 ^ 24 else if j.val = 2 then 33449169484642678123384 * 487149598837 * 10 ^ 24 else if j.val = 3 then 33449169484642678123384 * 12850498724 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_54 :
    (555839262800797352193228774017 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (54 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 4 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (54 : Fin 88) = fun j => if j.val = 0 then 27645452286518544907756 * 335954784 * 10 ^ 24 else if j.val = 1 then 27645452286518544907756 * 79859110825 * 10 ^ 24 else if j.val = 2 then 27645452286518544907756 * 839609875420 * 10 ^ 24 else if j.val = 3 then 27645452286518544907756 * 79859158060 * 10 ^ 24 else if j.val = 4 then 27645452286518544907756 * 335900911 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_55 :
    (693147180559945225548268000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (55 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (55 : Fin 88) = fun j => if j.val = 0 then 9195576949172513149155 * 499999995421 * 10 ^ 24 else if j.val = 1 then 9195576949172513149155 * 500000004579 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_56 :
    (809254626938009287581158899794 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (56 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (56 : Fin 88) = fun j => if j.val = 0 then 38142841962791472127125 * 12391042721 * 10 ^ 24 else if j.val = 1 then 38142841962791472127125 * 487608957904 * 10 ^ 24 else if j.val = 2 then 38142841962791472127125 * 487608978989 * 10 ^ 24 else if j.val = 3 then 38142841962791472127125 * 12391020386 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_57 :
    (904174067446698632161002067269 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (57 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (57 : Fin 88) = fun j => if j.val = 0 then 1030478265515958914250 * 180482819310 * 10 ^ 24 else if j.val = 1 then 1030478265515958914250 * 639034371429 * 10 ^ 24 else if j.val = 2 then 1030478265515958914250 * 180482809261 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_58 :
    (810262922464722712891004123417 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (58 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (58 : Fin 88) = fun j => if j.val = 0 then 38035970983486911204704 * 12528526979 * 10 ^ 24 else if j.val = 1 then 38035970983486911204704 * 487471462990 * 10 ^ 24 else if j.val = 2 then 38035970983486911204704 * 487471498999 * 10 ^ 24 else if j.val = 3 then 38035970983486911204704 * 12528511032 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_59 :
    (900135090685415182621685350433 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (59 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (59 : Fin 88) = fun j => if j.val = 0 then 2327957928531225148713 * 178894048726 * 10 ^ 24 else if j.val = 1 then 2327957928531225148713 * 642211618675 * 10 ^ 24 else if j.val = 2 then 2327957928531225148713 * 178894332599 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_60 :
    (693147032565648941175148952256 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (60 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (60 : Fin 88) = fun j => if j.val = 0 then 109658439634580542040 * 500270115771 * 10 ^ 24 else if j.val = 1 then 109658439634580542040 * 499729884229 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_61 :
    (693147177777170961385168000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (61 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (61 : Fin 88) = fun j => if j.val = 0 then 111367461157590711288 * 500026376004 * 10 ^ 24 else if j.val = 1 then 111367461157590711288 * 499973623996 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_62 :
    (913635271692005838891910421335 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (62 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (62 : Fin 88) = fun j => if j.val = 0 then 2827065221580752258364 * 184273544648 * 10 ^ 24 else if j.val = 1 then 2827065221580752258364 * 631452900978 * 10 ^ 24 else if j.val = 2 then 2827065221580752258364 * 184273554374 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_63 :
    (813666032907065811261810639461 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (63 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (63 : Fin 88) = fun j => if j.val = 0 then 5929939676816393897659 * 12995642506 * 10 ^ 24 else if j.val = 1 then 5929939676816393897659 * 487004369424 * 10 ^ 24 else if j.val = 2 then 5929939676816393897659 * 487004270051 * 10 ^ 24 else if j.val = 3 then 5929939676816393897659 * 12995718019 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_64 :
    (697107702383598967852042279033 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (64 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (64 : Fin 88) = fun j => if j.val = 2 then 109654091445344080362 * 114174628371 * 10 ^ 24 else if j.val = 3 then 109654091445344080362 * 770835709238 * 10 ^ 24 else if j.val = 4 then 109654091445344080362 * 114989662391 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_65 :
    (693147180559940541238528000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (65 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (65 : Fin 88) = fun j => if j.val = 0 then 3168357237648848182578 * 500000034526 * 10 ^ 24 else if j.val = 1 then 3168357237648848182578 * 499999965474 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_66 :
    (811363495015077106383636213823 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (66 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (66 : Fin 88) = fun j => if j.val = 0 then 22670058072685971562852 * 12678590339 * 10 ^ 24 else if j.val = 1 then 22670058072685971562852 * 487321235004 * 10 ^ 24 else if j.val = 2 then 22670058072685971562852 * 487320620528 * 10 ^ 24 else if j.val = 3 then 22670058072685971562852 * 12679554129 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_67 :
    (693147180559945295667968000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (67 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (67 : Fin 88) = fun j => if j.val = 0 then 10597616645179269995036 * 500000001854 * 10 ^ 24 else if j.val = 1 then 10597616645179269995036 * 499999998146 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_68 :
    (808063973333190131823627888319 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (68 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (68 : Fin 88) = fun j => if j.val = 0 then 31152707349587326905912 * 12229216813 * 10 ^ 24 else if j.val = 1 then 31152707349587326905912 * 487770785322 * 10 ^ 24 else if j.val = 2 then 31152707349587326905912 * 487770762642 * 10 ^ 24 else if j.val = 3 then 31152707349587326905912 * 12229235223 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_69 :
    (904442706875552098961590574012 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (69 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (69 : Fin 88) = fun j => if j.val = 0 then 7058076743104276513260 * 180589097958 * 10 ^ 24 else if j.val = 1 then 7058076743104276513260 * 638821815651 * 10 ^ 24 else if j.val = 2 then 7058076743104276513260 * 180589086391 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_70 :
    (810505974110958074747758371608 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (70 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (70 : Fin 88) = fun j => if j.val = 0 then 32885010632936733617999 * 12561708087 * 10 ^ 24 else if j.val = 1 then 32885010632936733617999 * 487438301875 * 10 ^ 24 else if j.val = 2 then 32885010632936733617999 * 487438250612 * 10 ^ 24 else if j.val = 3 then 32885010632936733617999 * 12561739426 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_71 :
    (693147180559933105796332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (71 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (71 : Fin 88) = fun j => if j.val = 0 then 538454767714302432280 * 500000055235 * 10 ^ 24 else if j.val = 1 then 538454767714302432280 * 499999944765 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_72 :
    (908478667143893967840054705234 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (72 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (72 : Fin 88) = fun j => if j.val = 0 then 2068050246907185572524 * 182195208189 * 10 ^ 24 else if j.val = 1 then 2068050246907185572524 * 635609621624 * 10 ^ 24 else if j.val = 2 then 2068050246907185572524 * 182195170187 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_73 :
    (693147180559945298354956000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (73 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (73 : Fin 88) = fun j => if j.val = 0 then 110305054882402779048 * 499999998337 * 10 ^ 24 else if j.val = 1 then 110305054882402779048 * 500000001663 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_74 :
    (693147177778038558778576000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (74 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (74 : Fin 88) = fun j => if j.val = 0 then 111445588322840301966 * 500026371892 * 10 ^ 24 else if j.val = 1 then 111445588322840301966 * 499973628108 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_75 :
    (913523360619795756146835727666 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (75 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (75 : Fin 88) = fun j => if j.val = 0 then 2821845899840507345252 * 184228120612 * 10 ^ 24 else if j.val = 1 then 2821845899840507345252 * 631543753637 * 10 ^ 24 else if j.val = 2 then 2821845899840507345252 * 184228125751 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_76 :
    (814027245896503449218869586820 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (76 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (76 : Fin 88) = fun j => if j.val = 0 then 5926568303523453246126 * 13045504509 * 10 ^ 24 else if j.val = 1 then 5926568303523453246126 * 486954510971 * 10 ^ 24 else if j.val = 2 then 5926568303523453246126 * 486954392933 * 10 ^ 24 else if j.val = 3 then 5926568303523453246126 * 13045591587 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_77 :
    (768128973218896905742050088500 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (77 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (77 : Fin 88) = fun j => if j.val = 1 then 425399815358641047798 * 7155307698 * 10 ^ 24 else if j.val = 2 then 425399815358641047798 * 492844889393 * 10 ^ 24 else if j.val = 3 then 425399815358641047798 * 492844398919 * 10 ^ 24 else if j.val = 4 then 425399815358641047798 * 7155403990 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_78 :
    (706244786852125191721474325205 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (78 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (78 : Fin 88) = fun j => if j.val = 2 then 110244773314003508516 * 116801504696 * 10 ^ 24 else if j.val = 3 then 110244773314003508516 * 766008474599 * 10 ^ 24 else if j.val = 4 then 110244773314003508516 * 117190020705 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_79 :
    (693147180559917386338828000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (79 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (79 : Fin 88) = fun j => if j.val = 0 then 3226796416394010791650 * 500000083551 * 10 ^ 24 else if j.val = 1 then 3226796416394010791650 * 499999916449 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_80 :
    (811866072115054199250437015241 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (80 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (80 : Fin 88) = fun j => if j.val = 0 then 26031955097479542659200 * 12747581400 * 10 ^ 24 else if j.val = 1 then 26031955097479542659200 * 487252316026 * 10 ^ 24 else if j.val = 2 then 26031955097479542659200 * 487251701589 * 10 ^ 24 else if j.val = 3 then 26031955097479542659200 * 12748400985 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_81 :
    (541172579877544830047349695708 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (81 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (81 : Fin 88) = fun j => if j.val = 0 then 18490136774775589144871 * 328370849 * 10 ^ 24 else if j.val = 1 then 18490136774775589144871 * 76797382852 * 10 ^ 24 else if j.val = 2 then 18490136774775589144871 * 845748521033 * 10 ^ 24 else if j.val = 3 then 18490136774775589144871 * 76797408091 * 10 ^ 24 else if j.val = 4 then 18490136774775589144871 * 328317175 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_82 :
    (693147180559943876340496000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (82 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (82 : Fin 88) = fun j => if j.val = 0 then 10625118709154371058818 * 499999981072 * 10 ^ 24 else if j.val = 1 then 10625118709154371058818 * 500000018928 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_83 :
    (808497660291525475555814380364 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (83 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (83 : Fin 88) = fun j => if j.val = 0 then 35377377812585378471616 * 12288101439 * 10 ^ 24 else if j.val = 1 then 35377377812585378471616 * 487711899508 * 10 ^ 24 else if j.val = 2 then 35377377812585378471616 * 487711913337 * 10 ^ 24 else if j.val = 3 then 35377377812585378471616 * 12288085716 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_84 :
    (904271063551114303975859915889 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (84 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (84 : Fin 88) = fun j => if j.val = 0 then 565802419399427803472 * 180521181686 * 10 ^ 24 else if j.val = 1 then 565802419399427803472 * 638957642231 * 10 ^ 24 else if j.val = 2 then 565802419399427803472 * 180521176083 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_85 :
    (809596572386078316263144968264 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (85 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else -6) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (85 : Fin 88) = fun j => if j.val = 0 then 38904769580362828608244 * 12437607001 * 10 ^ 24 else if j.val = 1 then 38904769580362828608244 * 487562389946 * 10 ^ 24 else if j.val = 2 then 38904769580362828608244 * 487562388864 * 10 ^ 24 else if j.val = 3 then 38904769580362828608244 * 12437614189 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_86 :
    (900203948629792680361522546310 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (86 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (86 : Fin 88) = fun j => if j.val = 0 then 2344679235493339615898 * 178921138036 * 10 ^ 24 else if j.val = 1 then 2344679235493339615898 * 642157740250 * 10 ^ 24 else if j.val = 2 then 2344679235493339615898 * 178921121714 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_2_87 :
    (693147031671891987757848793744 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (87 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 2) 0 (87 : Fin 88) = fun j => if j.val = 0 then 109671448171802031851 * 499728948890 * 10 ^ 24 else if j.val = 1 then 109671448171802031851 * 500271051110 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((908325359119530596334407931475 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (44 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943273061356000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (45 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147155156113274603046306473 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (46 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908832442499560987486825367967 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (47 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 6) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812705119321585476734271786928 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (48 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((769499735418699768720615863817 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (49 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((712145688982461635277570329004 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (50 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (36 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945056797996000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (51 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911389002611906535961335434213 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (52 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812610097014610981038876394507 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (53 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((555839262800797352193228774017 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (54 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 4 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945225548268000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (55 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809254626938009287581158899794 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (56 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904174067446698632161002067269 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (57 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((810262922464722712891004123417 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (58 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900135090685415182621685350433 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (59 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147032565648941175148952256 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (60 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147177777170961385168000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (61 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913635271692005838891910421335 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (62 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((813666032907065811261810639461 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (63 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((697107702383598967852042279033 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (64 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559940541238528000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (65 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811363495015077106383636213823 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (66 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945295667968000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (67 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808063973333190131823627888319 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (68 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904442706875552098961590574012 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (69 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((810505974110958074747758371608 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (70 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559933105796332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (71 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908478667143893967840054705234 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (72 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945298354956000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (73 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147177778038558778576000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (74 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913523360619795756146835727666 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (75 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((814027245896503449218869586820 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (76 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((768128973218896905742050088500 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (77 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((706244786852125191721474325205 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (78 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559917386338828000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (79 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811866072115054199250437015241 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (80 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((541172579877544830047349695708 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (81 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943876340496000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (82 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808497660291525475555814380364 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (83 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904271063551114303975859915889 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (84 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809596572386078316263144968264 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (85 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else -6) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900203948629792680361522546310 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (86 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147031671891987757848793744 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 2) 0 (87 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.cr_2_44, L3C.cr_2_45, L3C.cr_2_46, L3C.cr_2_47, L3C.cr_2_48, L3C.cr_2_49, L3C.cr_2_50, L3C.cr_2_51, L3C.cr_2_52, L3C.cr_2_53, L3C.cr_2_54, L3C.cr_2_55, L3C.cr_2_56, L3C.cr_2_57, L3C.cr_2_58, L3C.cr_2_59, L3C.cr_2_60, L3C.cr_2_61, L3C.cr_2_62, L3C.cr_2_63, L3C.cr_2_64, L3C.cr_2_65, L3C.cr_2_66, L3C.cr_2_67, L3C.cr_2_68, L3C.cr_2_69, L3C.cr_2_70, L3C.cr_2_71, L3C.cr_2_72, L3C.cr_2_73, L3C.cr_2_74, L3C.cr_2_75, L3C.cr_2_76, L3C.cr_2_77, L3C.cr_2_78, L3C.cr_2_79, L3C.cr_2_80, L3C.cr_2_81, L3C.cr_2_82, L3C.cr_2_83, L3C.cr_2_84, L3C.cr_2_85, L3C.cr_2_86, L3C.cr_2_87⟩
