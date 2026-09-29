-- Prove2me | solution 1 for mme_released_recursive_level3_mixture54
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T20:53:13.909836+00:00
-- url     : https://prove2.me/submissions/ea5cc0de-1206-48fa-8099-c17f5ba5d514

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_floor_data
import Theorems.Thm_mme_certified_floor_support
import Theorems.Thm_mme_certified_mixture_support
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3C

theorem mx_2_7_1 :
    (1870916532672733732800964583750 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 2 1 ⟨(7 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 2 1 ⟨(7 : Fin 88), complement (htotal3 2 (7 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 2 (7 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 2 (7 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 2 (7 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 2 (7 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 2 (7 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 2 (7 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 2 (7 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 2 (7 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 2 (7 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 2 (7 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 53115229701329074513531716037630000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 53115229701329074513531716037630000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 106230459402658149027063432075260000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 2 (7 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 53112884241456335420441700020870000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39120192680577236002532492055132693126835200000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 647650702165391902359920085700534613746329600000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39120192680577236002532492055132693126835200000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 725891087526546374364985069810800000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((842072621 : ℚ)/15625000000) else if 3 * (v 0).val + (v 1).val = 4 then ((6970427379 : ℚ)/7812500000) else if 3 * (v 0).val + (v 1).val = 6 then ((842072621 : ℚ)/15625000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 2 (7 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 362937392594533704227216409504760000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 780486135476623424350941202123460000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 780486135476623424350941202123460000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 2 (7 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 390235233676321859140748296269160000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10248932018263587062911676428313185000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10248932018263587062911676428313185000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 20497864036527174125823352856626370000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 2 (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10248946758011750015898745708423190000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 204487904105445360302887971267611056964960940000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10141665834677155081057881496828887886070078120000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 204487904105445360302887971267611056964960940000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 10550641642888045801663657439364110000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((9690780477 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((240309219523 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((9690780477 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 2 (7 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5275320481262196680784704575223990000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 10550641642888045801663657439364110000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10550641642888045801663657439364110000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 2 (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5275321161625849120878952864140120000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10248932018263587062911676428313185000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10248932018263587062911676428313185000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 20497864036527174125823352856626370000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 2 (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10248917278515424109924607148203180000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39660426601901398592214002561946631783504580000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 701165282272820627166513196999566736432990840000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39660426601901398592214002561946631783504580000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 780486135476623424350941202123460000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((50815030273 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((449184969727 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((50815030273 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 2 (7 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 390250901800301565210192905854300000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 725891087526546374364985069810800000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 725891087526546374364985069810800000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 2 (7 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 362953694932012670137768660306040000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 53115229701329074513531716037630000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 53115229701329074513531716037630000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 2 1 ⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 106230459402658149027063432075260000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 2 (7 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 53117575161201813606621732054390000000000000000000000000 := by decide +kernel
  have hn : n3 2 (7 : Fin 88) = 32661113361821047875230000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![0,0],![0,2]] = ((1084120341506388420901 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![0,0],![1,1]] = ((21988080318993611579099 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![0,0],![2,0]] = ((1084120341506388420901 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![0,1],![0,1]] = ((630844829681 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![0,1],![1,0]] = ((630844829681 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![0,2],![0,0]] = ((216823921970616280233 : ℚ)/50000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![1,0],![0,1]] = ((630844829681 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![1,0],![1,0]] = ((630844829681 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![1,1],![0,0]] = ((4397615203904383719767 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88)
      ![![2,0],![0,0]] = ((216823921970616280233 : ℚ)/50000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 2) (n3 2) (m3 2)
      (mu3 2 1) (7 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 2) (n3 2) (m3 2)
        (mu3 2 1) (7 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_2_7_2 :
    (1702310753970766386894097825714 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 2 2 ⟨(7 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 2 2 ⟨(7 : Fin 88), complement (htotal3 2 (7 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 2 (7 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 2 (7 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 2 (7 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 2 (7 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 2 (7 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 2 (7 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 2 (7 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 2 (7 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 2 (7 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 2 (7 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 53115229701329074513531716037630000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 53115229701329074513531716037630000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 106230459402658149027063432075260000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 2 (7 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 53112884241456335420441700020870000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39120192680577236002532492055132693126835200000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 647650702165391902359920085700534613746329600000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39120192680577236002532492055132693126835200000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 725891087526546374364985069810800000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((842072621 : ℚ)/15625000000) else if 3 * (v 0).val + (v 1).val = 4 then ((6970427379 : ℚ)/7812500000) else if 3 * (v 0).val + (v 1).val = 6 then ((842072621 : ℚ)/15625000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 2 (7 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 362937392594533704227216409504760000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 390243067738311712175470601061730000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 390243067738311712175470601061730000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 780486135476623424350941202123460000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 2 (7 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 390235233676321859140748296269160000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 20497864036527174125823352856626370000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 20497864036527174125823352856626370000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 2 (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10248946758011750015898745708423190000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 5275320821444022900831828719682055000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 5275320821444022900831828719682055000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 10550641642888045801663657439364110000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 2 (7 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5275320481262196680784704575223990000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 600467237175781858376849121857908129535412220000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9349707168536482084909959195648293740929175560000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 600467237175781858376849121857908129535412220000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10550641642888045801663657439364110000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((28456432201 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((221543567799 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((28456432201 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 2 (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5275321161625849120878952864140120000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10248932018263587062911676428313185000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10248932018263587062911676428313185000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 20497864036527174125823352856626370000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 2 (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10248917278515424109924607148203180000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 780486135476623424350941202123460000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 780486135476623424350941202123460000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 2 (7 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 390250901800301565210192905854300000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 362945543763273187182492534905400000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 362945543763273187182492534905400000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 725891087526546374364985069810800000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 2 (7 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 362953694932012670137768660306040000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 106230459402658149027063432075260000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 2 2 ⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 106230459402658149027063432075260000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 2 (7 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 53117575161201813606621732054390000000000000000000000000 := by decide +kernel
  have hn : n3 2 (7 : Fin 88) = 32661113361821047875230000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![0,0],![1,2]] = ((13574812103 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![0,0],![2,1]] = ((13574812103 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![0,1],![0,2]] = ((4895640441169770752669 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![0,1],![1,1]] = ((116710681415580229247331 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![0,1],![2,0]] = ((4895640441169770752669 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![0,2],![0,1]] = ((1223906896016349439277 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![0,2],![1,0]] = ((1223906896016349439277 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![1,0],![0,2]] = ((4895640441169770752669 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![1,0],![1,1]] = ((116710681415580229247331 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![1,0],![2,0]] = ((4895640441169770752669 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq10 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![1,1],![0,1]] = ((29177700085796150560723 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq11 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![1,1],![1,0]] = ((29177700085796150560723 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq12 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![1,2],![0,0]] = ((13574188761 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq13 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![2,0],![0,1]] = ((1223906896016349439277 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq14 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![2,0],![1,0]] = ((1223906896016349439277 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq15 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88)
      ![![2,1],![0,0]] = ((13574188761 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 2) (n3 2) (m3 2)
      (mu3 2 2) (7 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 2) (n3 2) (m3 2)
        (mu3 2 2) (7 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_2_8_1 :
    (1891606329579620300187544938749 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 2 1 ⟨(8 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 2 1 ⟨(8 : Fin 88), complement (htotal3 2 (8 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 2 (8 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 2 (8 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 2 (8 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 2 (8 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 2 (8 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 2 (8 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 2 (8 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 2 (8 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 2 (8 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(8 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 66893610580083906008024588951612710080000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10888513637104693465351459149862096774579840000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 66893610580083906008024588951612710080000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 2 1 ⟨(8 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 10888647424325853633163475199040000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(8 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((6143427 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((499993856573 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((6143427 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 2 (8 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5444680516798425413771658752960000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(8 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 659285003351946633943372995030240000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 659285003351946633943372995030240000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 2 1 ⟨(8 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 1318570006703893267886745990060480000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(8 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 2 (8 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 659285033708958243441683022679040000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(8 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 149175341056565990310273723547866025920000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1225873371878886626115393616629832904267948160000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 149175341056565990310273723547866025920000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 2 1 ⟨(8 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1225873670229568739247374237177280000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(8 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((121689 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((499999878311 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((121689 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 2 (8 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 612936691397319584792806548401920000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(8 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4781416511088576390107234115298240000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 2 1 ⟨(8 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 4781416511088576390107234115298240000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(8 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 2 (8 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2390708924947455246847592911535360000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(8 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 9229151087881499338565482182264960000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9229151087881499338565482182264960000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 2 1 ⟨(8 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 18458302175762998677130964364529920000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(8 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 2 (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9229151087881499338565482182264960000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 190913242193065057816568594858374580478026880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 4399590026702446274474096925581490839043946240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 190913242193065057816568594858374580478026880000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 2 1 ⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 4781416511088576390107234115298240000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((19964088231 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((230035911769 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((19964088231 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 2 (8 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2390707586141121143259641203762880000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(8 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1225873670229568739247374237177280000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 2 1 ⟨(8 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 1225873670229568739247374237177280000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(8 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 2 (8 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 612936978832249154454567688775360000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 659285003351946633943372995030240000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 659285003351946633943372995030240000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 2 1 ⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 1318570006703893267886745990060480000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 2 (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 659284972994935024445062967381440000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(8 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 10888647424325853633163475199040000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 2 1 ⟨(8 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 10888647424325853633163475199040000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(8 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 2 (8 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 5443966907527428219391816446080000000000000000000000000 := by decide +kernel
  have hn : n3 2 (8 : Fin 88) = 16565899923327863589440000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![0,0],![0,2]] = ((5762243904568128612633 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![0,0],![1,1]] = ((85059561267931871387367 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![0,0],![2,0]] = ((5762243904568128612633 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![0,1],![0,1]] = ((636712834401 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![0,1],![1,0]] = ((636712834401 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![0,2],![0,0]] = ((5762240677955220462219 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![1,0],![0,1]] = ((636712834401 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![1,0],![1,0]] = ((636712834401 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![1,1],![0,0]] = ((85059536949044779537781 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88)
      ![![2,0],![0,0]] = ((5762240677955220462219 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 2) (n3 2) (m3 2)
      (mu3 2 1) (8 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 2) (n3 2) (m3 2)
        (mu3 2 1) (8 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_2_8_2 :
    (1891789996443156552688612896061 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 2 2 ⟨(8 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 2 2 ⟨(8 : Fin 88), complement (htotal3 2 (8 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 2 (8 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 2 (8 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 2 (8 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 2 (8 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 2 (8 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 2 (8 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 2 (8 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 2 (8 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 2 (8 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(8 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 66893610580083906008024588951612710080000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10888513637104693465351459149862096774579840000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 66893610580083906008024588951612710080000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 2 2 ⟨(8 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 10888647424325853633163475199040000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(8 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((6143427 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((499993856573 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((6143427 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 2 (8 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5444680516798425413771658752960000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(8 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 1318570006703893267886745990060480000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 2 2 ⟨(8 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 1318570006703893267886745990060480000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(8 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 2 (8 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 659285033708958243441683022679040000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(8 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 612936835114784369623687118588640000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 612936835114784369623687118588640000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 2 2 ⟨(8 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1225873670229568739247374237177280000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(8 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 2 (8 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 612936691397319584792806548401920000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(8 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 192439805061685973644992437054794786024019840000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 4396536900965204442817249241188650427951960320000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 192439805061685973644992437054794786024019840000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 2 2 ⟨(8 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 4781416511088576390107234115298240000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(8 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((20123723233 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((229876276767 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((20123723233 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 2 (8 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2390708924947455246847592911535360000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(8 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 9229151087881499338565482182264960000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9229151087881499338565482182264960000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 2 2 ⟨(8 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 18458302175762998677130964364529920000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(8 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 2 (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9229151087881499338565482182264960000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4781416511088576390107234115298240000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 2 2 ⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 4781416511088576390107234115298240000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 2 (8 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2390707586141121143259641203762880000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(8 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 612936835114784369623687118588640000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 612936835114784369623687118588640000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 2 2 ⟨(8 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 1225873670229568739247374237177280000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(8 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 2 (8 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 612936978832249154454567688775360000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1318570006703893267886745990060480000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 2 2 ⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 1318570006703893267886745990060480000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 2 (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 659284972994935024445062967381440000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(8 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 10888647424325853633163475199040000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 2 2 ⟨(8 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 10888647424325853633163475199040000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(8 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 2 (8 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 5443966907527428219391816446080000000000000000000000000 := by decide +kernel
  have hn : n3 2 (8 : Fin 88) = 16565899923327863589440000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![0,0],![0,2]] = ((1452077905200197460599 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![0,0],![1,1]] = ((21603087677299802539401 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![0,0],![2,0]] = ((1452077905200197460599 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![0,1],![0,1]] = ((631117223121 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![0,1],![1,0]] = ((631117223121 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![0,2],![0,0]] = ((5808314873743311289997 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![1,0],![0,1]] = ((631117223121 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![1,0],![1,0]] = ((631117223121 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![1,1],![0,0]] = ((86412411235756688710003 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88)
      ![![2,0],![0,0]] = ((5808314873743311289997 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 2) (n3 2) (m3 2)
      (mu3 2 2) (8 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 2) (n3 2) (m3 2)
        (mu3 2 2) (8 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_2_9_1 :
    (1847061516271904927648005293137 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 2 1 ⟨(9 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 2 1 ⟨(9 : Fin 88), complement (htotal3 2 (9 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 2 (9 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 2 (9 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 2 (9 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 2 (9 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 2 (9 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 2 (9 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 2 (9 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 2 (9 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(9 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4700973428036232584330179312640000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 2 1 ⟨(9 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 4700973428036232584330179312640000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(9 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 2 (9 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2350495382343530664697505085440000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(9 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 439629556544527830665976331752832000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 439629556544527830665976331752832000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 2 1 ⟨(9 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 879259113089055661331952663505664000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(9 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 2 (9 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 439629700005313438531387807104768000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(9 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 281025737782935292230104074669820889991951360000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5542375429017378627838017734579974220016097280000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 281025737782935292230104074669820889991951360000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 2 1 ⟨(9 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 6104426904583249212298225883919616000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(9 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2301819173 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((22698180827 : ℚ)/25000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2301819173 : ℚ)/50000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 2 (9 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3052213287296139663073922589930240000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(9 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 87759155016991602028745636631040000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 87759155016991602028745636631040000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 2 1 ⟨(9 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 175518310033983204057491273262080000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(9 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 2 (9 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87759351236357800097888494981120000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(9 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 175518310033983204057491273262080000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 2 1 ⟨(9 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 175518310033983204057491273262080000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(9 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 2 (9 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87758958797625403959602778280960000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(9 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 3052213452291624606149112941959808000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3052213452291624606149112941959808000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 2 1 ⟨(9 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 6104426904583249212298225883919616000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(9 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 2 (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3052213617287109549224303293989376000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(9 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 18531756684095802149567932225410309731889664000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 842195599720864057032816799054843380536220672000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18531756684095802149567932225410309731889664000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 2 1 ⟨(9 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 879259113089055661331952663505664000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(9 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((10538279563 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((239461720437 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10538279563 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 2 (9 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 439629413083742222800564856400896000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2350486714018116292165089656320000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2350486714018116292165089656320000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 2 1 ⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4700973428036232584330179312640000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 2 (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2350478045692701919632674227200000000000000000000000000 := by decide +kernel
  have hn : n3 2 (9 : Fin 88) = 7163905301134324310272000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![0,0],![1,2]] = ((125782587 : ℚ)/20000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![0,0],![2,1]] = ((125782587 : ℚ)/20000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![0,1],![0,2]] = ((10453708665666958186937 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![0,1],![1,1]] = ((111401730878583041813063 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![0,1],![2,0]] = ((10453708665666958186937 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![0,2],![0,1]] = ((5226853591655678875117 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![0,2],![1,0]] = ((5226853591655678875117 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![1,0],![0,2]] = ((10453708665666958186937 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![1,0],![1,1]] = ((111401730878583041813063 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![1,0],![2,0]] = ((10453708665666958186937 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![1,1],![0,1]] = ((55700855416219321124883 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![1,1],![1,0]] = ((55700855416219321124883 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![1,2],![0,0]] = ((628915553 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![2,0],![0,1]] = ((5226853591655678875117 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![2,0],![1,0]] = ((5226853591655678875117 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88)
      ![![2,1],![0,0]] = ((628915553 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 2) (n3 2) (m3 2)
      (mu3 2 1) (9 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 2) (n3 2) (m3 2)
        (mu3 2 1) (9 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_2_9_2 :
    (1102402474501938708513925398794 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -3 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -3 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 2 2 ⟨(9 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 2 2 ⟨(9 : Fin 88), complement (htotal3 2 (9 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 2 (9 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 2 (9 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 2 (9 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 2 (9 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 2 (9 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 2 (9 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 2 (9 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 2 (9 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(9 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 4700973428036232584330179312640000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 2 2 ⟨(9 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 4700973428036232584330179312640000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(9 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 2 (9 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2350495382343530664697505085440000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(9 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 439629556544527830665976331752832000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 439629556544527830665976331752832000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 2 2 ⟨(9 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 879259113089055661331952663505664000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(9 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 2 (9 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 439629700005313438531387807104768000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(9 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 281025737782935292230104074669820889991951360000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5542375429017378627838017734579974220016097280000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 281025737782935292230104074669820889991951360000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 2 2 ⟨(9 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 6104426904583249212298225883919616000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(9 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2301819173 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((22698180827 : ℚ)/25000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2301819173 : ℚ)/50000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 2 (9 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3052213287296139663073922589930240000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(9 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 87759155016991602028745636631040000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 87759155016991602028745636631040000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 2 2 ⟨(9 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 175518310033983204057491273262080000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(9 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 2 (9 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87759351236357800097888494981120000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(9 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 87759155016991602028745636631040000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 87759155016991602028745636631040000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 2 2 ⟨(9 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 175518310033983204057491273262080000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(9 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 2 (9 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87758958797625403959602778280960000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(9 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1665760539000473926515186703201369077853440000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6101095383505248264445195510513213261844293120000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1665760539000473926515186703201369077853440000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 2 2 ⟨(9 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 6104426904583249212298225883919616000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(9 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((54575493 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((99945424507 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((54575493 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 2 (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3052213617287109549224303293989376000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(9 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 439629556544527830665976331752832000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 439629556544527830665976331752832000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 2 2 ⟨(9 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 879259113089055661331952663505664000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(9 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 2 (9 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 439629413083742222800564856400896000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 2 ⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4700973428036232584330179312640000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 2 2 ⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4700973428036232584330179312640000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 2) ⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 2 (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2350478045692701919632674227200000000000000000000000000 := by decide +kernel
  have hn : n3 2 (9 : Fin 88) = 7163905301134324310272000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![0,0],![2,2]] = ((3281001 : ℚ)/10000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![0,1],![1,2]] = ((18404373807 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![0,1],![2,1]] = ((18404373807 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![0,2],![0,2]] = ((107044395064546423921568988717 : ℚ)/10000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![0,2],![1,1]] = ((98544274730982178979428431011283 : ℚ)/5000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![0,2],![2,0]] = ((107044395064546423921568988717 : ℚ)/10000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![1,0],![1,2]] = ((18404373807 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![1,0],![2,1]] = ((18404373807 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![1,1],![0,2]] = ((98544285271004062217853431011283 : ℚ)/5000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![1,1],![1,1]] = ((1933076449735449212378796568988717 : ℚ)/2500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![1,1],![2,0]] = ((98544285271004062217853431011283 : ℚ)/5000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![1,2],![0,1]] = ((73617480499 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![1,2],![1,0]] = ((73617480499 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![2,0],![0,2]] = ((107044395064546423921568988717 : ℚ)/10000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![2,0],![1,1]] = ((98544274730982178979428431011283 : ℚ)/5000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![2,0],![2,0]] = ((107044395064546423921568988717 : ℚ)/10000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq16 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![2,1],![0,1]] = ((73617480499 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq17 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![2,1],![1,0]] = ((73617480499 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq18 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88)
      ![![2,2],![0,0]] = ((8202563 : ℚ)/25000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 2) (n3 2) (m3 2)
      (mu3 2 2) (9 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 2) (n3 2) (m3 2)
        (mu3 2 2) (9 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_2_10_1 :
    (1720416215067652422654982022124 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 2 1 ⟨(10 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 2 1 ⟨(10 : Fin 88), complement (htotal3 2 (10 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (10 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (10 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 2 (10 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 2 (10 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 2 (10 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 2 (10 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 2 (10 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 2 (10 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 2 (10 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 2 (10 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 2 (10 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 2 (10 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 18372212174516975143293043983672696588795360000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 622117083055782809957631149704714606822409280000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18372212174516975143293043983672696588795360000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 658861507404816760244217237672060000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((3485598257 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((59014401743 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((3485598257 : ℚ)/125000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 2 (10 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 329430738559022718992771459380190000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 46595664516101824670260910854730000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 46595664516101824670260910854730000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 93191329032203649340521821709460000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 2 (10 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46595654685113552727425093627350000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 4988453560927316819925801038047545000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 4988453560927316819925801038047545000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 9976907121854633639851602076095090000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 2 (10 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4988455127061757477427905070359030000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 149122359265971933260359231517388525635309520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 18793264072740611401453692697075042948729380960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 149122359265971933260359231517388525635309520000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 19091508791272555267974411160109820000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((1952731459 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((123047268541 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1952731459 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 2 (10 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9545754410535415139291876011132430000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 355275364259565864939623852206785000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 355275364259565864939623852206785000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 710550728519131729879247704413570000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 2 (10 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 355275306693328639013484307541490000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 710550728519131729879247704413570000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 710550728519131729879247704413570000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 2 (10 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 355275421825803090865763396872080000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 9545754395636277633987205580054910000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9545754395636277633987205580054910000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 19091508791272555267974411160109820000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 2 (10 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9545754380737140128682535148977390000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 514987485717324908901859347211657841544369570000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8946932150419983822047883381671774316911260860000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 514987485717324908901859347211657841544369570000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 9976907121854633639851602076095090000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((51617949273 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((448382050727 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((51617949273 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 2 (10 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4988451994792876162423697005736060000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 93191329032203649340521821709460000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 93191329032203649340521821709460000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 2 (10 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46595674347090096613096728082110000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 2 1 ⟨(10 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 329430753702408380122108618836030000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 329430753702408380122108618836030000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 2 1 ⟨(10 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 658861507404816760244217237672060000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 2 1) ⟨(10 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 2 (10 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 329430768845794041251445778291870000000000000000000000000 := by decide +kernel
  have hn : n3 2 (10 : Fin 88) = 30531019478083341047290000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![0,0],![1,2]] = ((13162714611 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![0,0],![2,1]] = ((13162714611 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![0,1],![0,2]] = ((2235373174946932839871 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![0,1],![1,1]] = ((46448360715153067160129 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![0,1],![2,0]] = ((2235373174946932839871 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![0,2],![0,1]] = ((223537211181123005657 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![0,2],![1,0]] = ((223537211181123005657 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![1,0],![0,2]] = ((2235373174946932839871 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![1,0],![1,1]] = ((46448360715153067160129 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![1,0],![2,0]] = ((2235373174946932839871 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq10 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![1,1],![0,1]] = ((4644835151738876994343 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq11 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![1,1],![1,0]] = ((4644835151738876994343 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq12 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![1,2],![0,0]] = ((3290677549 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq13 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![2,0],![0,1]] = ((223537211181123005657 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq14 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![2,0],![1,0]] = ((223537211181123005657 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq15 : mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88)
      ![![2,1],![0,0]] = ((3290677549 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 2) (n3 2) (m3 2)
      (mu3 2 1) (10 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 2) (n3 2) (m3 2)
        (mu3 2 1) (10 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1870916532672733732800964583750 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (7 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1702310753970766386894097825714 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (7 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1891606329579620300187544938749 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (8 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1891789996443156552688612896061 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (8 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1847061516271904927648005293137 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (9 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1102402474501938708513925398794 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 2) (9 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -3 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -5 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -3 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1720416215067652422654982022124 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 2) (n3 2) (m3 2) (mu3 2 1) (10 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_2_7_1, L3C.mx_2_7_2, L3C.mx_2_8_1, L3C.mx_2_8_2, L3C.mx_2_9_1, L3C.mx_2_9_2, L3C.mx_2_10_1⟩
