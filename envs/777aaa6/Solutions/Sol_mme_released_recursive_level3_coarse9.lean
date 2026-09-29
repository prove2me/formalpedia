-- Prove2me | solution 1 for mme_released_recursive_level3_coarse9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T10:38:11.533119+00:00
-- url     : https://prove2.me/submissions/6811ad50-6606-45b9-9ea4-af326c13c61b

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

theorem cr_4_0 :
    (695669369271058284567787966781 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (0 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (0 : Fin 88) = fun j => if j.val = 2 then 109663991759174306340 * 114204991409 * 10 ^ 24 else if j.val = 3 then 109663991759174306340 * 771590185990 * 10 ^ 24 else if j.val = 4 then 109663991759174306340 * 114204822601 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_1 :
    (811853802924915988459743364486 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (1 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (1 : Fin 88) = fun j => if j.val = 0 then 4422383363210048759118 * 12746197777 * 10 ^ 24 else if j.val = 1 then 4422383363210048759118 * 487253843534 * 10 ^ 24 else if j.val = 2 then 4422383363210048759118 * 487253541622 * 10 ^ 24 else if j.val = 3 then 4422383363210048759118 * 12746417067 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_2 :
    (909028802561712503675482039394 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (2 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 3) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (2 : Fin 88) = fun j => if j.val = 0 then 3131204594009091410301 * 182415426452 * 10 ^ 24 else if j.val = 1 then 3131204594009091410301 * 635169004091 * 10 ^ 24 else if j.val = 2 then 3131204594009091410301 * 182415569457 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_3 :
    (693147125745428790457875602407 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (3 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (3 : Fin 88) = fun j => if j.val = 0 then 110610239989241785364 * 500159313845 * 10 ^ 24 else if j.val = 1 then 110610239989241785364 * 499840686155 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_4 :
    (811315135345153628435154288720 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (4 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -7) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (4 : Fin 88) = fun j => if j.val = 0 then 26379718789689124429117 * 12672542392 * 10 ^ 24 else if j.val = 1 then 26379718789689124429117 * 487327489994 * 10 ^ 24 else if j.val = 2 then 26379718789689124429117 * 487327617528 * 10 ^ 24 else if j.val = 3 then 26379718789689124429117 * 12672350086 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_5 :
    (911570245883450418890941477203 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (5 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (5 : Fin 88) = fun j => if j.val = 0 then 11851337476953424060920 * 183437600791 * 10 ^ 24 else if j.val = 1 then 11851337476953424060920 * 633124721643 * 10 ^ 24 else if j.val = 2 then 11851337476953424060920 * 183437677566 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_6 :
    (693147180559945034852332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (6 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (6 : Fin 88) = fun j => if j.val = 0 then 3459350499599621513215 * 499999991715 * 10 ^ 24 else if j.val = 1 then 3459350499599621513215 * 500000008285 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_7 :
    (808245403451173076401937082854 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (7 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 3) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (7 : Fin 88) = fun j => if j.val = 0 then 28240753413816587652194 * 12253843137 * 10 ^ 24 else if j.val = 1 then 28240753413816587652194 * 487746155540 * 10 ^ 24 else if j.val = 2 then 28240753413816587652194 * 487746158215 * 10 ^ 24 else if j.val = 3 then 28240753413816587652194 * 12253843108 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_8 :
    (693147180559945291133056000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (8 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (8 : Fin 88) = fun j => if j.val = 0 then 9290955795545665556742 * 500000002138 * 10 ^ 24 else if j.val = 1 then 9290955795545665556742 * 499999997862 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_9 :
    (811596422819819972301783649462 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (9 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (9 : Fin 88) = fun j => if j.val = 0 then 30078798681238086381800 * 12711011289 * 10 ^ 24 else if j.val = 1 then 30078798681238086381800 * 487288984863 * 10 ^ 24 else if j.val = 2 then 30078798681238086381800 * 487289014100 * 10 ^ 24 else if j.val = 3 then 30078798681238086381800 * 12710989748 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_10 :
    (904526051801826186618685990665 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (10 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (10 : Fin 88) = fun j => if j.val = 0 then 8424673049500239260700 * 180622026527 * 10 ^ 24 else if j.val = 1 then 8424673049500239260700 * 638755840543 * 10 ^ 24 else if j.val = 2 then 8424673049500239260700 * 180622132930 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_11 :
    (911391733358412288973669122010 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (11 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (11 : Fin 88) = fun j => if j.val = 0 then 1782535350888865451044 * 183365557605 * 10 ^ 24 else if j.val = 1 then 1782535350888865451044 * 633268787280 * 10 ^ 24 else if j.val = 2 then 1782535350888865451044 * 183365655115 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_12 :
    (693147180559943248075628000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (12 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (12 : Fin 88) = fun j => if j.val = 0 then 1032678586558085421312 * 500000022701 * 10 ^ 24 else if j.val = 1 then 1032678586558085421312 * 499999977299 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_13 :
    (693147180559945297569868000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (13 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (13 : Fin 88) = fun j => if j.val = 0 then 110882501168321360874 * 499999998279 * 10 ^ 24 else if j.val = 1 then 110882501168321360874 * 500000001721 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_14 :
    (705302718657212482970351087589 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (14 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (14 : Fin 88) = fun j => if j.val = 2 then 110334936725859517500 * 116745198387 * 10 ^ 24 else if j.val = 3 then 110334936725859517500 * 766509626500 * 10 ^ 24 else if j.val = 4 then 110334936725859517500 * 116745175113 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_15 :
    (768122001448974932684734835875 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (15 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (15 : Fin 88) = fun j => if j.val = 1 then 431067241066959747014 * 7154458383 * 10 ^ 24 else if j.val = 2 then 431067241066959747014 * 492845497089 * 10 ^ 24 else if j.val = 3 then 431067241066959747014 * 492845438457 * 10 ^ 24 else if j.val = 4 then 431067241066959747014 * 7154606071 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_16 :
    (809134773132695634560864335090 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (16 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (16 : Fin 88) = fun j => if j.val = 0 then 1076773881111635640384 * 12374671813 * 10 ^ 24 else if j.val = 1 then 1076773881111635640384 * 487625324729 * 10 ^ 24 else if j.val = 2 then 1076773881111635640384 * 487625241350 * 10 ^ 24 else if j.val = 3 then 1076773881111635640384 * 12374762108 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_17 :
    (900610304103560969829806931246 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (17 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (17 : Fin 88) = fun j => if j.val = 0 then 3460528501721079753364 * 179080201304 * 10 ^ 24 else if j.val = 1 then 3460528501721079753364 * 641839578304 * 10 ^ 24 else if j.val = 2 then 3460528501721079753364 * 179080220392 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_18 :
    (693146831513764335565064694636 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (18 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (18 : Fin 88) = fun j => if j.val = 0 then 109598577872823727092 * 500417757887 * 10 ^ 24 else if j.val = 1 then 109598577872823727092 * 499582242113 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_19 :
    (541185030310113003149889450570 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (19 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (19 : Fin 88) = fun j => if j.val = 0 then 18647285340698424068913 * 328638390 * 10 ^ 24 else if j.val = 1 then 18647285340698424068913 * 76799026487 * 10 ^ 24 else if j.val = 2 then 18647285340698424068913 * 845744669952 * 10 ^ 24 else if j.val = 3 then 18647285340698424068913 * 76799026741 * 10 ^ 24 else if j.val = 4 then 18647285340698424068913 * 328638430 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_20 :
    (811799288703544469931333685812 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (20 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (20 : Fin 88) = fun j => if j.val = 0 then 32421242698599578649164 * 12738896706 * 10 ^ 24 else if j.val = 1 then 32421242698599578649164 * 487261133415 * 10 ^ 24 else if j.val = 2 then 32421242698599578649164 * 487261212771 * 10 ^ 24 else if j.val = 3 then 32421242698599578649164 * 12738757108 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_21 :
    (911343963373787536139146831205 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (21 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (21 : Fin 88) = fun j => if j.val = 0 then 35108911211614823817312 * 183346350728 * 10 ^ 24 else if j.val = 1 then 35108911211614823817312 * 633307328478 * 10 ^ 24 else if j.val = 2 then 35108911211614823817312 * 183346320794 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_22 :
    (693147180559945059081548000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (22 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (22 : Fin 88) = fun j => if j.val = 0 then 3858657751759982394332 * 499999992089 * 10 ^ 24 else if j.val = 1 then 3858657751759982394332 * 500000007911 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_23 :
    (808689015859258705557281359923 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (23 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (23 : Fin 88) = fun j => if j.val = 0 then 30384626793716358340490 * 12314089174 * 10 ^ 24 else if j.val = 1 then 30384626793716358340490 * 487685908104 * 10 ^ 24 else if j.val = 2 then 30384626793716358340490 * 487685905701 * 10 ^ 24 else if j.val = 3 then 30384626793716358340490 * 12314097021 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_24 :
    (693147180559944889822976000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (24 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (24 : Fin 88) = fun j => if j.val = 0 then 7130226375930017905045 * 500000010242 * 10 ^ 24 else if j.val = 1 then 7130226375930017905045 * 499999989758 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_25 :
    (812097632779688235913446814819 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (25 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (25 : Fin 88) = fun j => if j.val = 0 then 29929106028889441524672 * 12779788086 * 10 ^ 24 else if j.val = 1 then 29929106028889441524672 * 487220209508 * 10 ^ 24 else if j.val = 2 then 29929106028889441524672 * 487220227286 * 10 ^ 24 else if j.val = 3 then 29929106028889441524672 * 12779775120 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_26 :
    (904408159415713284658404201478 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (26 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (26 : Fin 88) = fun j => if j.val = 0 then 8164110236649356450706 * 180575420797 * 10 ^ 24 else if j.val = 1 then 8164110236649356450706 * 638849160158 * 10 ^ 24 else if j.val = 2 then 8164110236649356450706 * 180575419045 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_27 :
    (911281309933911292955216068470 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (27 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (27 : Fin 88) = fun j => if j.val = 0 then 1783041239240708438996 * 183321069796 * 10 ^ 24 else if j.val = 1 then 1783041239240708438996 * 633357865473 * 10 ^ 24 else if j.val = 2 then 1783041239240708438996 * 183321064731 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_28 :
    (693147180559943233885868000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (28 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (28 : Fin 88) = fun j => if j.val = 0 then 1030965504516986976075 * 500000022779 * 10 ^ 24 else if j.val = 1 then 1030965504516986976075 * 499999977221 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_29 :
    (693147180559945297666048000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (29 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (29 : Fin 88) = fun j => if j.val = 0 then 110876309922998052675 * 499999998286 * 10 ^ 24 else if j.val = 1 then 110876309922998052675 * 500000001714 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_30 :
    (695670881237055574086707642991 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (30 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (30 : Fin 88) = fun j => if j.val = 2 then 109719873022450608880 * 114205320935 * 10 ^ 24 else if j.val = 3 then 109719873022450608880 * 771589394605 * 10 ^ 24 else if j.val = 4 then 109719873022450608880 * 114205284460 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_31 :
    (813661635104783897440245740584 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (31 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (31 : Fin 88) = fun j => if j.val = 0 then 5924622315078773553208 * 12995000655 * 10 ^ 24 else if j.val = 1 then 5924622315078773553208 * 487005011215 * 10 ^ 24 else if j.val = 2 then 5924622315078773553208 * 487004841870 * 10 ^ 24 else if j.val = 3 then 5924622315078773553208 * 12995146260 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_32 :
    (913639102893697258136557809038 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (32 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (32 : Fin 88) = fun j => if j.val = 0 then 2852852408763104434800 * 184275097144 * 10 ^ 24 else if j.val = 1 then 2852852408763104434800 * 631449790153 * 10 ^ 24 else if j.val = 2 then 2852852408763104434800 * 184275112703 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_33 :
    (693147175096488814038028000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (33 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (33 : Fin 88) = fun j => if j.val = 0 then 111371395039279837175 * 499963042401 * 10 ^ 24 else if j.val = 1 then 111371395039279837175 * 500036957599 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_34 :
    (811377522406426906244615507773 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (34 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -2) else if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (34 : Fin 88) = fun j => if j.val = 0 then 22343909623700462424900 * 12681097222 * 10 ^ 24 else if j.val = 1 then 22343909623700462424900 * 487318934638 * 10 ^ 24 else if j.val = 2 then 22343909623700462424900 * 487319076616 * 10 ^ 24 else if j.val = 3 then 22343909623700462424900 * 12680891524 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_35 :
    (693147180559945298880716000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (35 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (35 : Fin 88) = fun j => if j.val = 0 then 3204803582879214136392 * 499999998377 * 10 ^ 24 else if j.val = 1 then 3204803582879214136392 * 500000001623 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_36 :
    (808083922188805489925780196523 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (36 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -2) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (36 : Fin 88) = fun j => if j.val = 0 then 30945654421230948857778 * 12231937311 * 10 ^ 24 else if j.val = 1 then 30945654421230948857778 * 487768058375 * 10 ^ 24 else if j.val = 2 then 30945654421230948857778 * 487768077494 * 10 ^ 24 else if j.val = 3 then 30945654421230948857778 * 12231926820 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_37 :
    (693147180559945170271616000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (37 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (37 : Fin 88) = fun j => if j.val = 0 then 10579856008931009917324 * 500000005898 * 10 ^ 24 else if j.val = 1 then 10579856008931009917324 * 499999994102 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_38 :
    (810510024149896048286767809858 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (38 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (38 : Fin 88) = fun j => if j.val = 0 then 33099802441880096977626 * 12562291792 * 10 ^ 24 else if j.val = 1 then 33099802441880096977626 * 487437699414 * 10 ^ 24 else if j.val = 2 then 33099802441880096977626 * 487437746044 * 10 ^ 24 else if j.val = 3 then 33099802441880096977626 * 12562262750 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_39 :
    (904413986296019121309740468186 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (39 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (39 : Fin 88) = fun j => if j.val = 0 then 7249411247529971479884 * 180577732155 * 10 ^ 24 else if j.val = 1 then 7249411247529971479884 * 638844548142 * 10 ^ 24 else if j.val = 2 then 7249411247529971479884 * 180577719703 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_40 :
    (908495916247890182422996443557 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (40 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (40 : Fin 88) = fun j => if j.val = 0 then 2069487094319678026602 * 182202093103 * 10 ^ 24 else if j.val = 1 then 2069487094319678026602 * 635595815801 * 10 ^ 24 else if j.val = 2 then 2069487094319678026602 * 182202091096 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_41 :
    (693147180559943131888336000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (41 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (41 : Fin 88) = fun j => if j.val = 0 then 586212289303707866358 * 499999976668 * 10 ^ 24 else if j.val = 1 then 586212289303707866358 * 500000023332 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_42 :
    (693147180559943259682156000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (42 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (42 : Fin 88) = fun j => if j.val = 0 then 110217471991083150788 * 499999977363 * 10 ^ 24 else if j.val = 1 then 110217471991083150788 * 500000022637 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_43 :
    (705299089213330417227946216475 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (43 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (43 : Fin 88) = fun j => if j.val = 2 then 110354343848059076483 * 116742943888 * 10 ^ 24 else if j.val = 3 then 110354343848059076483 * 766511555068 * 10 ^ 24 else if j.val = 4 then 110354343848059076483 * 116745501044 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((695669369271058284567787966781 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (0 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811853802924915988459743364486 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (1 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((909028802561712503675482039394 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (2 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 3) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147125745428790457875602407 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (3 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811315135345153628435154288720 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (4 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -7) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911570245883450418890941477203 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (5 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945034852332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (6 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808245403451173076401937082854 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (7 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 3) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945291133056000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (8 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811596422819819972301783649462 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (9 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904526051801826186618685990665 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (10 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911391733358412288973669122010 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (11 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943248075628000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (12 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945297569868000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (13 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((705302718657212482970351087589 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (14 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((768122001448974932684734835875 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (15 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809134773132695634560864335090 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (16 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900610304103560969829806931246 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (17 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693146831513764335565064694636 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (18 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((541185030310113003149889450570 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (19 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811799288703544469931333685812 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (20 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911343963373787536139146831205 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (21 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945059081548000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (22 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808689015859258705557281359923 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (23 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559944889822976000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (24 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812097632779688235913446814819 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (25 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904408159415713284658404201478 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (26 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911281309933911292955216068470 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (27 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943233885868000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (28 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945297666048000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (29 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((695670881237055574086707642991 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (30 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((813661635104783897440245740584 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (31 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913639102893697258136557809038 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (32 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147175096488814038028000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (33 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811377522406426906244615507773 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (34 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -2) else if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945298880716000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (35 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808083922188805489925780196523 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (36 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -2) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945170271616000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (37 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((810510024149896048286767809858 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (38 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904413986296019121309740468186 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (39 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908495916247890182422996443557 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (40 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943131888336000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (41 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943259682156000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (42 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((705299089213330417227946216475 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (43 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.cr_4_0, L3C.cr_4_1, L3C.cr_4_2, L3C.cr_4_3, L3C.cr_4_4, L3C.cr_4_5, L3C.cr_4_6, L3C.cr_4_7, L3C.cr_4_8, L3C.cr_4_9, L3C.cr_4_10, L3C.cr_4_11, L3C.cr_4_12, L3C.cr_4_13, L3C.cr_4_14, L3C.cr_4_15, L3C.cr_4_16, L3C.cr_4_17, L3C.cr_4_18, L3C.cr_4_19, L3C.cr_4_20, L3C.cr_4_21, L3C.cr_4_22, L3C.cr_4_23, L3C.cr_4_24, L3C.cr_4_25, L3C.cr_4_26, L3C.cr_4_27, L3C.cr_4_28, L3C.cr_4_29, L3C.cr_4_30, L3C.cr_4_31, L3C.cr_4_32, L3C.cr_4_33, L3C.cr_4_34, L3C.cr_4_35, L3C.cr_4_36, L3C.cr_4_37, L3C.cr_4_38, L3C.cr_4_39, L3C.cr_4_40, L3C.cr_4_41, L3C.cr_4_42, L3C.cr_4_43⟩
