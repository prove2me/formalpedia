-- Prove2me | solution 1 for mme_released_recursive_level3_penalty11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:00:57.169516+00:00
-- url     : https://prove2.me/submissions/5739dbb9-3dad-45e5-85c0-67039f7ebdac

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

theorem pn_1_64 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 8) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (64 : Fin 88)), (alphaG (n3 1) (m3 1) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 8) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (34354928453073129425220 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (64 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (64 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (64 : Fin 88) = 7533124791762000018720000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (64 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1077838629340410272762413448304480000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (64 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((143079885059 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 280087365257816232246119977109760000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((4647596001 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (64 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2529185577791404691751088236960000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (64 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((335741893 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (64 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 316422609434230015882463950697760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (64 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((42004164033 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4179369186130368647636931005669760000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((138699719627 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (64 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 316422639807789176266848026176800000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (64 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((8400833613 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (64 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2529174089776097254701059688960000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (64 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((20983773 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (64 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 280087405929156982969158078179040000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (64 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((37180773407 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (64 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1077838596194661189009613365936480000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (64 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143079880659 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_65 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 5) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (65 : Fin 88)), (alphaG (n3 1) (m3 1) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 5) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2852042611551896715238 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (65 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (65 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (65 : Fin 88) = 34569217330078390243885000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (65 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11054495817200553532208033129345000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (65 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((319778597 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1255076068241376339905078270355620000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((9076543853 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (65 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5072084810353145442974590472052690000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (65 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((73361290797 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1267885413751960336249613906026335000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((36676717371 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19357015566247590100216829954039780000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((139987372157 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (65 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1267886556299162312670489856669470000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (65 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((18338375211 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5072084833652797923447425496431180000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((36680645567 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (65 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1255077203805596415650119391733985000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (65 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((36306208261 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (65 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11052381909560819238644619561595000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (65 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((319717447 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_66 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (66 : Fin 88)), (alphaG (n3 1) (m3 1) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2769931061770804435191 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (66 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (66 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (66 : Fin 88) = 3460947237936582430296000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (66 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22883585067226255918504666159920000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (66 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((661194277 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (66 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 596926094893659671563276361202552000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (66 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((172474774637 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (66 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1110663949732880778031687924124832000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (66 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((80228321423 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1110664056773056952934309328319520000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((16045665831 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 596926081569012805507434004562952000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((172474770787 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (66 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22883469900745966340787715630224000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (66 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3305954747 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_67 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (67 : Fin 88)), (alphaG (n3 1) (m3 1) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2919387103891079587501 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (67 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (67 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (67 : Fin 88) = 29809684317932394972832000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (67 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 371250160130566261322180827526272000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (67 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3113502949 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (67 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 9731725018254725335017779160352000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (67 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((326461861 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12577695596488720738249332150137472000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((105483300849 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (67 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 1946164690743013704579046980950304000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (67 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((65286323397 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (67 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1946164633418990761195051448194368000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (67 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((32643160737 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (67 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 12577695598187872744371478663588896000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (67 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((421933203453 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (67 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9731751966209348745902834600480000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (67 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((65292553 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (67 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 371250161978766689033989315841856000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (67 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((6227005929 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_68 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (68 : Fin 88)), (alphaG (n3 1) (m3 1) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3207558698233583309600106 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (68 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (68 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (68 : Fin 88) = 30645330975296276558990000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (68 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 330563897157908390281333870998200000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((539338109 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (68 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46743315705931997786654583811490000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1525299751 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (68 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5007441396317417031551405265206110000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163399814489 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (68 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9581360736994860904597397443334760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((78163299531 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (68 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 356556333250501198682307542808860000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((5817465857 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (68 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 356555292718933263472533258862400000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((72718111 : ℚ)/6250000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (68 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9581362868316339574502839567971280000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((39081658459 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (68 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5007441411333629209446580779111210000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((163399814979 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46743001897742810752782619753890000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1525289511 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (68 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 330562721603012177916165068141800000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (68 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((539336191 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_69 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (69 : Fin 88)), (alphaG (n3 1) (m3 1) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (809800813667906521333800 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (69 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (69 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (69 : Fin 88) = 32467402339806471476382000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (69 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 52803171971421719105176374830130000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((325268843 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 360778932100485913447232559636390000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2222407129 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (69 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 387950272127684420355044743487904000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((746807267 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10188225157628706162932520979913898000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313798592539 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (69 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5243944433799013011396029516837418000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161514135899 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5243944062534267255709028184409248000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((10094632779 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (69 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10188229327547058273636878577559686000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313798720973 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (69 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 387947657040762960642799678299714000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((11948835727 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (69 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 360776839381600698881307077958198000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11111971189 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (69 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 52802485675471060275982307067414000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (69 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1626323077 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_70 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (70 : Fin 88)), (alphaG (n3 1) (m3 1) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (498334698239354444066 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (70 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (70 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (70 : Fin 88) = 1074418333028316277361000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (70 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 347493909448014813224606751789000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (70 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((323425149 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (70 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 12948940341867733412111640374768000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (70 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((753252943 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (70 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 66126873043113028547153580471968000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (70 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((1923333509 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (70 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 457785873966120982721651079181200000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (70 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1065194673 : ℚ)/2500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (70 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 457785826988253789391550167848836000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (70 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((106519456369 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (70 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 66126841638939572462497109487299000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (70 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((61546643059 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (70 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12948997770602052108644981597579000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (70 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12052100539 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (70 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 347485369971103904166834286561000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (70 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((323417201 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_71 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (71 : Fin 88)), (alphaG (n3 1) (m3 1) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6966972256781759558178 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (71 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (71 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (71 : Fin 88) = 18215036851192609762712000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (71 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5986055393094198578113281441712000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (71 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((164316313 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (71 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 725338252490907877719758975301712000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (71 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((19910425063 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (71 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 673586036020719902331068010531408000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (71 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((18489834567 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (71 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2628700070977653358254069468994824000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (71 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((144314836827 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (71 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10147816007511570934634826668748720000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (71 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((55711202181 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (71 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2628700048536727957584774241333640000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (71 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((28862967119 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (71 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 673586747791499899533487098265520000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (71 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((3697970821 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (71 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 725339012476890420029016104934488000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (71 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((39820891849 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (71 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 5984619993545214046886150447976000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (71 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((328553823 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_72 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (72 : Fin 88)), (alphaG (n3 1) (m3 1) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2653147701083016742752 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (72 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (72 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (72 : Fin 88) = 388711251414280888052000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (72 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2782578472896440890842784837748000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (72 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7158471649 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (72 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 68364009706844357472195651807464000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (72 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((87936751841 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (72 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 123209014681673266291430929874592000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (72 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((39620995737 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (72 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 123209031487215509936450843914760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (72 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((31696800913 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (72 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 68364033478480937712543360627524000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (72 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((175873564837 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (72 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 2782583587170375748536428937912000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (72 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((3579242403 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_73 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (73 : Fin 88)), (alphaG (n3 1) (m3 1) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2796134065577732759219 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (73 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (73 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (73 : Fin 88) = 110276215462816003680000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12873566804453362047389729436960000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((116739287347 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (73 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42264541352620831479080044767840000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (73 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((383260716513 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (73 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42264541354716079572873548837760000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (73 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((95815179133 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (73 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12873565951025730580656676957440000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (73 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((14592409951 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_74 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (74 : Fin 88)), (alphaG (n3 1) (m3 1) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3770153105453002405818 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (74 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (74 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (74 : Fin 88) = 110932621619304688218000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (74 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42309172173238100933675974616124000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (74 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((190697612459 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (74 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13154924723134385279875250745054000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (74 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((118584817803 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (74 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13156885933455251101914530414928000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (74 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((14825312137 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (74 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42311638789476950902534244223894000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (74 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((381417460183 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_75 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (75 : Fin 88)), (alphaG (n3 1) (m3 1) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10392249829072792650806 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (75 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (75 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (75 : Fin 88) = 1033373886421894910635000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (75 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 182920901530737244811894620713525000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (75 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((35402656083 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (75 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 326194532027580432918768129386010000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (75 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((157829869863 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (75 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7571527289221897149317689708010000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (75 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((3663498463 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (75 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7571544008178005569155448871675000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (75 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1465402621 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (75 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 326194474851003297195322723951460000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (75 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((78914921099 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (75 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 182920906715174032990541387369320000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (75 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((22126660679 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_76 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 4) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (76 : Fin 88)), (alphaG (n3 1) (m3 1) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 4) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3335210422431398302079 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (76 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (76 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (76 : Fin 88) = 9516551606480965455444000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (76 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3146193677873373169132955723208000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (76 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((165301141 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (76 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 619899705788476825546119755205708000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (76 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((65139110407 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (76 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4015134223287793517160484327650600000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (76 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((8438212473 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (76 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 120094280744345972593458947439744000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (76 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((394359893 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (76 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 120097004638362640820758362809532000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (76 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12619802803 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4015132370005984016237828638119708000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((421910428907 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (76 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 619902038913851428452015639133968000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (76 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((16284838893 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (76 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3145789424277681464201373917532000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (76 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((330559803 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_77 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (77 : Fin 88)), (alphaG (n3 1) (m3 1) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5268638063820807621085 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (77 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (77 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (77 : Fin 88) = 3518866750156645750632000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (77 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 24891092091754442745278392460232000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (77 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7073610301 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (77 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1116457074404429383537546980302496000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (77 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((79319362857 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 618085013738968226109542768992800000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1756488829 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (77 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 618085187965098759865387174284384000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (77 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((43912233103 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1116457085699991651540379839831216000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((158638727319 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 24891296256403286833864844128872000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7073668321 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_78 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (78 : Fin 88)), (alphaG (n3 1) (m3 1) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7919853780447087833777 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (78 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (78 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (78 : Fin 88) = 110603207133145928684000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (78 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12998805762485322889838328688396000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (78 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((117526481369 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (78 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42317361987064761455064322954852000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (78 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((382605198203 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (78 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42320335664891743216502920978852000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (78 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((382632084203 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12966703718704101122594427377900000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((4689449449 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_79 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -8) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (79 : Fin 88)), (alphaG (n3 1) (m3 1) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -8) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3401352672754398030474 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (79 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (79 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (79 : Fin 88) = 1778577919082657708650000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (79 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 313234812127142816062027301503150000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (79 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((176115315931 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (79 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12898875584831057051793540445650000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (79 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7252353381 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 563155467311075489667005258064050000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((316632440597 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (79 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 563155127467521023029100920056650000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (79 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((316632249521 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (79 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12898510058611438860311889532250000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (79 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((1450429573 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (79 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 313235126533475883979761090398250000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (79 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((35223098541 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 8) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (64 : Fin 88)), (alphaG (n3 1) (m3 1) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 8) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (34354928453073129425220 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 5) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (65 : Fin 88)), (alphaG (n3 1) (m3 1) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 5) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2852042611551896715238 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (66 : Fin 88)), (alphaG (n3 1) (m3 1) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2769931061770804435191 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (67 : Fin 88)), (alphaG (n3 1) (m3 1) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2919387103891079587501 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (68 : Fin 88)), (alphaG (n3 1) (m3 1) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3207558698233583309600106 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (69 : Fin 88)), (alphaG (n3 1) (m3 1) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (809800813667906521333800 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (70 : Fin 88)), (alphaG (n3 1) (m3 1) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (498334698239354444066 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (71 : Fin 88)), (alphaG (n3 1) (m3 1) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6966972256781759558178 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (72 : Fin 88)), (alphaG (n3 1) (m3 1) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2653147701083016742752 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (73 : Fin 88)), (alphaG (n3 1) (m3 1) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2796134065577732759219 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (74 : Fin 88)), (alphaG (n3 1) (m3 1) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3770153105453002405818 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (75 : Fin 88)), (alphaG (n3 1) (m3 1) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10392249829072792650806 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 4) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (76 : Fin 88)), (alphaG (n3 1) (m3 1) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 4) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3335210422431398302079 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (77 : Fin 88)), (alphaG (n3 1) (m3 1) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5268638063820807621085 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (78 : Fin 88)), (alphaG (n3 1) (m3 1) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7919853780447087833777 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -8) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (79 : Fin 88)), (alphaG (n3 1) (m3 1) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -8) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3401352672754398030474 : ℚ)/10^30) :=
  ⟨L3C.pn_1_64, L3C.pn_1_65, L3C.pn_1_66, L3C.pn_1_67, L3C.pn_1_68, L3C.pn_1_69, L3C.pn_1_70, L3C.pn_1_71, L3C.pn_1_72, L3C.pn_1_73, L3C.pn_1_74, L3C.pn_1_75, L3C.pn_1_76, L3C.pn_1_77, L3C.pn_1_78, L3C.pn_1_79⟩
