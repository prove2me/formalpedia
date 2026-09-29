-- Prove2me | solution 1 for mme_released_recursive_level3_penalty12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:01:12.295526+00:00
-- url     : https://prove2.me/submissions/5be4f414-1292-43f4-84dd-ff9c1a83aa7f

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_generic_rate_data
import Definitions.Def_mme_certified_entropy_rational_data
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3C

theorem pn_1_80 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -7) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 0) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (80 : Fin 88)), (alphaG (n3 1) (m3 1) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -7) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 0) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (23104628325442969281288 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (80 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (80 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (80 : Fin 88) = 7717995443772407539770000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (80 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1104289455868608534903708937680990000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (80 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((143079827387 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (80 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 287320666062183142350191661578250000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (80 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1489094769 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (80 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2591360823896697346297418473140000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (80 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((167877841 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 323823772470888752505992475858510000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((41956978963 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (80 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4281944126690395470571989808836210000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (80 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((554800032973 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (80 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 323823756263098320583936642341510000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (80 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((41956976863 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2591350713322666004443541374440000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((83938593 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 287320912791061488866515892945610000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((37227401193 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (80 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1104290042088952466636923620911340000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (80 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((71539951671 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_81 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (81 : Fin 88)), (alphaG (n3 1) (m3 1) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4800475067056628005538 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (81 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (81 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (81 : Fin 88) = 10088568715741724989248000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (81 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3366747436525655204130677914176000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (81 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((333719037 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (81 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 389546354924763815680266656274048000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (81 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((19306324113 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1457745172581450015277725467610048000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((144494745851 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (81 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 392790040375835290088560763815296000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (81 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((19467084551 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5601670897801100418534502334154240000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((13881232947 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 392790420270978850058956958937984000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((19467103379 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1457745990976232804962198320397056000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((36123706743 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 389546961953943441859859259326208000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((9653177099 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3366129420894697581799561570944000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((166828889 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_82 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (82 : Fin 88)), (alphaG (n3 1) (m3 1) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (741105374598970132234 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (82 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (82 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (82 : Fin 88) = 3184747525107641881986000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22520697401429365247046503431788000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3535711579 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 558409697914658399850562122345888000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((10958672813 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1011445094940972314115358858453422000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((317590354327 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1011432369333180984050142102558594000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((317586358529 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (82 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 558404448488943269874232761058116000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (82 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((87668558353 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (82 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22535217028457548848657652152192000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (82 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((110562223 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_83 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (83 : Fin 88)), (alphaG (n3 1) (m3 1) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5897613718627934126676 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (83 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (83 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (83 : Fin 88) = 30101001568275166394438000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (83 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 372839923899905867369184244062830000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (83 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((2477259257 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (83 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 9774900548097535160659188757798000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (83 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((324736721 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12700774944520539350510544127729668000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((210969308043 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (83 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 1967110929381185974594388215301404000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (83 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((32675174029 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1967111285596438533562707327080696000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((16337589973 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 12700775258895399729576381951240140000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((42193862653 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (83 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9774922281020667455329325542034000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (83 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((324737443 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (83 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 372839403152578736208805620285430000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (83 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((2477255797 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_84 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -7) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (84 : Fin 88)), (alphaG (n3 1) (m3 1) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -7) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3152656439863101988780889 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (84 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (84 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (84 : Fin 88) = 28280326715507336906540000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 303414010950536694860700952239960000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5364400737 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (84 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42942825416989961916379504370260000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1518469919 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4620285816891385701970402850763640000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((81687277933 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 8844291523089802821879088467777860000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((312736539859 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (84 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 329229229962274243169525693377460000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11641634599 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 329228786922675918031585715521820000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11641618933 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8844292654755356669620682119882500000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((2501892639 : ℚ)/8000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (84 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4620285957048684904024764559575880000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((81687280411 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (84 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42942655056301827700181979373300000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((303692779 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (84 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 303413255413328163366688157117320000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (84 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((5364387379 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_85 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (85 : Fin 88)), (alphaG (n3 1) (m3 1) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (817293448503796544729993 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (85 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (85 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (85 : Fin 88) = 26334963324960967239696000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (85 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42854204717552508523661580542352000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1627274137 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (85 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 290840666439035203900392225604320000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1104389867 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (85 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 316773809550500787128935614811824000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12028640619 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 8263501095415464032191119287362368000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((78446104077 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4253512558057505654558321707365312000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((40378948943 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4253512366918341841991621481651744000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((80757894257 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8263504933446684048677523833417712000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313784562047 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (85 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 316771598993679289905345514729584000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12028556679 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 290838523958093901700902440136240000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2208763463 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (85 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42853567464109971118176314378544000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (85 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1627249939 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_86 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (86 : Fin 88)), (alphaG (n3 1) (m3 1) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1189902160900013701034 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (86 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (86 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (86 : Fin 88) = 4346066586434418366955000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (86 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1415296010191578931855671311940000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (86 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((81412467 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (86 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 53983284349753169477631289762940000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (86 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((3105295517 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (86 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 283552360705283239475918584067370000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (86 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((32621723007 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (86 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1834082338066379388958144527556595000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (86 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((422009718809 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (86 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1834082392066256725405792736972470000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (86 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((211004865617 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 283552452189984883920425208470120000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((8155433383 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (86 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 53983191135317023632226155312100000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (86 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((621058031 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (86 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1415271911252357153005826546465000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (86 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((325644323 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_87 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (87 : Fin 88)), (alphaG (n3 1) (m3 1) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9912331728696826810851 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (87 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (87 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (87 : Fin 88) = 109612094878156526164000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (87 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12522910611058108618846085699512000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (87 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((57123762779 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (87 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42245713810085693820526718390900000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (87 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((15416442449 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (87 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42322296998274033303354088517760000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (87 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((2413185849 : ℚ)/6250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (87 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12521173458738690421273107391828000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (87 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((114231677377 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -7) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 0) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (80 : Fin 88)), (alphaG (n3 1) (m3 1) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -7) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 0) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (23104628325442969281288 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (81 : Fin 88)), (alphaG (n3 1) (m3 1) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4800475067056628005538 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (82 : Fin 88)), (alphaG (n3 1) (m3 1) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (741105374598970132234 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (83 : Fin 88)), (alphaG (n3 1) (m3 1) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5897613718627934126676 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -7) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (84 : Fin 88)), (alphaG (n3 1) (m3 1) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -7) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3152656439863101988780889 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (85 : Fin 88)), (alphaG (n3 1) (m3 1) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (817293448503796544729993 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (86 : Fin 88)), (alphaG (n3 1) (m3 1) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1189902160900013701034 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (87 : Fin 88)), (alphaG (n3 1) (m3 1) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9912331728696826810851 : ℚ)/10^30) :=
  ⟨L3C.pn_1_80, L3C.pn_1_81, L3C.pn_1_82, L3C.pn_1_83, L3C.pn_1_84, L3C.pn_1_85, L3C.pn_1_86, L3C.pn_1_87⟩
