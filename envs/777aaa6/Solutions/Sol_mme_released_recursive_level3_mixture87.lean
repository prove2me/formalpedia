-- Prove2me | solution 1 for mme_released_recursive_level3_mixture87
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T18:55:58.383136+00:00
-- url     : https://prove2.me/submissions/651b383d-b570-419a-924d-0cb9022fb32e

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

theorem mx_3_31_2 :
    (1882658275868060309977927402536 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(31 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(31 : Fin 88), complement (htotal3 3 (31 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (31 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (31 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (31 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (31 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (31 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (31 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (31 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (31 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 3 (31 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(31 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 7664082980905464050666861167574399563290168000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 202955586400307467041130690122415200873419664000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 7664082980905464050666861167574399563290168000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(31 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 218283752362118395142464412457564000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(31 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((17555321681 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((232444678319 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((17555321681 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (31 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 109141874733794266108981942920186000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(31 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 25402346814639976795537438666704000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 25402346814639976795537438666704000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(31 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 50804693629279953591074877333408000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(31 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (31 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 25402349905573697808052319902142000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 476316799549535696031910271880000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 476316799549535696031910271880000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (31 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 238157773970839795711661713544000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(31 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 56384220405446447722760574299984000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(31 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 56384220405446447722760574299984000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(31 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (31 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 28192109977194839288831484508508000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(31 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 420833747176283822289668225637164000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 420833747176283822289668225637164000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(31 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 841667494352567644579336451274328000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(31 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (31 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 420833747176283822289668225637164000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 56384220405446447722760574299984000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 56384220405446447722760574299984000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (31 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 28192110428251608433929089791476000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(31 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 19801462244816248400795440491483940881360000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 436713875059903199230319390897032118237280000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 19801462244816248400795440491483940881360000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 2 ⟨(31 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 476316799549535696031910271880000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(31 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((20786021261 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((229213978739 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((20786021261 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (31 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 238159025578695900320248558336000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(31 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 25402346814639976795537438666704000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 25402346814639976795537438666704000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 2 ⟨(31 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 50804693629279953591074877333408000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(31 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (31 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 25402343723706255783022557431266000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(31 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 218283752362118395142464412457564000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 3 2 ⟨(31 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 218283752362118395142464412457564000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(31 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 3 (31 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 109141877628324129033482469537378000000000000000000000000 := by decide +kernel
  have hn : n3 3 (31 : Fin 88) = 746782730372678154442000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![0,0],![0,2]] = ((2572329333631144364881 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![0,0],![1,1]] = ((43482614171118855635119 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![0,0],![2,0]] = ((2572329333631144364881 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![0,1],![0,1]] = ((315780227383 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![0,1],![1,0]] = ((315780227383 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![0,2],![0,0]] = ((2572329300424089162761 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![1,0],![0,1]] = ((315780227383 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![1,0],![1,0]] = ((315780227383 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![1,1],![0,0]] = ((43482613503325910837239 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88)
      ![![2,0],![0,0]] = ((2572329300424089162761 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (31 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (31 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_32_1 :
    (1718060822912193513620831254767 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(32 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(32 : Fin 88), complement (htotal3 3 (32 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (32 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (32 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (32 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (32 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (32 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (32 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (32 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (32 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 3 (32 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 3 (32 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 22641591913507182293523584918375241790113138000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 784069669469694711791161802119966516419773724000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 22641591913507182293523584918375241790113138000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 829352853296709076378208971956717000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((13650156157 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((236349843843 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((13650156157 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (32 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 414668202689909646814027972565943000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 57688707943250629195259094505128000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 57688707943250629195259094505128000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 115377415886501258390518189010256000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (32 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 57686393235351260061218165080041000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 6231358276910486375419908858178246500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 6231358276910486375419908858178246500000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 12462716553820972750839817716356493000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6231358154982434858940021670668717000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 180725507692786781913293151409512207390354750000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 23479142379561706795191364729543100585219290500000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 180725507692786781913293151409512207390354750000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 23840593394947280359017951032362125000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((3790289627 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((246209710373 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((3790289627 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (32 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11920312355783934656144967761865159000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 436172405715512171310252045157204500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 436172405715512171310252045157204500000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 872344811431024342620504090314409000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (32 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 436164175238481439910770120125552000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 872344811431024342620504090314409000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 872344811431024342620504090314409000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (32 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 436180636192542902709733970188857000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 11920296697473640179508975516181062500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 11920296697473640179508975516181062500000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 23840593394947280359017951032362125000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (32 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11920281039163345702872983270496966000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 644300870340258166688929403790680678590248921000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 11174114813140456417461958908775131642819502158000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 644300870340258166688929403790680678590248921000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 12462716553820972750839817716356493000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((51698268797 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((448301731203 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((51698268797 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (32 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 6231358398838537891899796045687776000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 115377415886501258390518189010256000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 115377415886501258390518189010256000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 3 (32 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 57691022651149998329300023930215000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 414676426648354538189104485978358500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 414676426648354538189104485978358500000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 3 1 ⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 829352853296709076378208971956717000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 3 (32 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 414684650606799429564180999390774000000000000000000000000 := by decide +kernel
  have hn : n3 3 (32 : Fin 88) = 38120385029382487787247000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![0,0],![1,2]] = ((404861843 : ℚ)/62500000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![0,0],![2,1]] = ((404861843 : ℚ)/62500000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![0,1],![0,2]] = ((11118305446303735970967 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![0,1],![1,1]] = ((232403944269196264029033 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![0,1],![2,0]] = ((11118305446303735970967 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![0,2],![0,1]] = ((138978752815747432171 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![0,2],![1,0]] = ((138978752815747432171 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![1,0],![0,2]] = ((11118305446303735970967 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![1,0],![1,1]] = ((232403944269196264029033 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![1,0],![2,0]] = ((11118305446303735970967 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq10 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![1,1],![0,1]] = ((2905051846396752567829 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq11 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![1,1],![1,0]] = ((2905051846396752567829 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq12 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![1,2],![0,0]] = ((12955025719 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq13 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![2,0],![0,1]] = ((138978752815747432171 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq14 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![2,0],![1,0]] = ((138978752815747432171 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq15 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88)
      ![![2,1],![0,0]] = ((12955025719 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (32 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (32 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_32_2 :
    (1864164245230100361525207695287 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(32 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(32 : Fin 88), complement (htotal3 3 (32 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (32 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (32 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (32 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (32 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (32 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (32 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (32 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (32 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 3 (32 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 3 (32 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 22641591913507182293523584918375241790113138000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 784069669469694711791161802119966516419773724000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 22641591913507182293523584918375241790113138000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 829352853296709076378208971956717000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((13650156157 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((236349843843 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((13650156157 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (32 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 414668202689909646814027972565943000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 57688707943250629195259094505128000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 57688707943250629195259094505128000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 115377415886501258390518189010256000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (32 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 57686393235351260061218165080041000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 226647494483544033619557402287729159109870618000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 12009421564853884683600702911781034681780258764000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 226647494483544033619557402287729159109870618000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 12462716553820972750839817716356493000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((9093021313 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((240906978687 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((9093021313 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6231358154982434858940021670668717000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 11920296697473640179508975516181062500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 11920296697473640179508975516181062500000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 23840593394947280359017951032362125000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (32 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11920312355783934656144967761865159000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 872344811431024342620504090314409000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 872344811431024342620504090314409000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (32 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 436164175238481439910770120125552000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 48531254081990966172089697778006338734366853000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 775282303267042410276324694758396322531266294000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 48531254081990966172089697778006338734366853000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 872344811431024342620504090314409000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((55633109117 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((444366890883 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((55633109117 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (32 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 436180636192542902709733970188857000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 11920296697473640179508975516181062500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 11920296697473640179508975516181062500000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 23840593394947280359017951032362125000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (32 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11920281039163345702872983270496966000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 12462716553820972750839817716356493000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 12462716553820972750839817716356493000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (32 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 6231358398838537891899796045687776000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 57688707943250629195259094505128000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 57688707943250629195259094505128000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 115377415886501258390518189010256000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 3 (32 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 57691022651149998329300023930215000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 829352853296709076378208971956717000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 3 2 ⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 829352853296709076378208971956717000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 3 (32 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 414684650606799429564180999390774000000000000000000000000 := by decide +kernel
  have hn : n3 3 (32 : Fin 88) = 38120385029382487787247000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![0,0],![0,2]] = ((976576830032934303717 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![0,0],![1,1]] = ((22246585853217065696283 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![0,0],![2,0]] = ((976576830032934303717 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![0,1],![0,1]] = ((628429403123 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![0,1],![1,0]] = ((628429403123 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![0,2],![0,0]] = ((3906319447658980835179 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![1,0],![0,1]] = ((628429403123 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![1,0],![1,0]] = ((628429403123 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![1,1],![0,0]] = ((88986328257841019164821 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88)
      ![![2,0],![0,0]] = ((3906319447658980835179 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (32 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (32 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_33_1 :
    (1892796802049574741255828867354 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(33 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(33 : Fin 88), complement (htotal3 3 (33 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (33 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (33 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (33 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (33 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (33 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (33 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (33 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (33 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 3 (33 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 209376553407347403635017813674301354500000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 18726981939396905367625982754392651397291000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 209376553407347403635017813674301354500000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 18727400692503720062433252790020000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((447209 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((19999552791 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((447209 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (33 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9364359934009983202943355585747000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(33 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1152041380997031729005797248031170000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1152041380997031729005797248031170000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(33 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2304082761994063458011594496062340000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(33 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1152041048317682741989937953072251000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(33 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 554045656617910918939567727487053009610000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2148753595773066212837502916641283025893980780000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 554045656617910918939567727487053009610000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(33 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 2148754703864379448659340795776738000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(33 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((51569 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((99999948431 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((51569 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (33 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1074377038349912224459194796639905000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(33 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 7973911786854366731146467168501192000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(33 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 7973911786854366731146467168501192000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(33 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (33 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3986955911799402504301420232652333000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(33 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 15433459824179188384763164286869710000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 15433459824179188384763164286869710000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 1 ⟨(33 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 30866919648358376769526328573739420000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(33 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (33 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15433459824179188384763164286869710000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 326335133114392158196271989284921007062054024000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7321241520625582414753923189931349985875891952000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 326335133114392158196271989284921007062054024000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 1 ⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 7973911786854366731146467168501192000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((40925350297 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((459074649703 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((40925350297 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (33 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3986955875054964226845046935848859000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(33 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 2148754703864379448659340795776738000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 1 ⟨(33 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 2148754703864379448659340795776738000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(33 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (33 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1074377665514467224200145999136833000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1152041380997031729005797248031170000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1152041380997031729005797248031170000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 1 ⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 2304082761994063458011594496062340000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (33 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1152041713676380716021656542990089000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 18727400692503720062433252790020000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 3 1 ⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 18727400692503720062433252790020000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 3 (33 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9363040758493736859489897204273000000000000000000000000 := by decide +kernel
  have hn : n3 3 (33 : Fin 88) = 27878936477584501742643000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![0,0],![0,2]] = ((5852732192423804259977 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![0,0],![1,1]] = ((85088624594076195740023 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![0,0],![2,0]] = ((5852732192423804259977 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![0,1],![0,1]] = ((12724690987 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![0,1],![1,0]] = ((12724690987 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![0,2],![0,0]] = ((5852732139007417973961 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![1,0],![0,1]] = ((12724690987 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![1,0],![1,0]] = ((12724690987 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![1,1],![0,0]] = ((85088636399492582026039 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88)
      ![![2,0],![0,0]] = ((5852732139007417973961 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (33 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (33 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_33_2 :
    (1893039170324468033792469580543 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(33 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(33 : Fin 88), complement (htotal3 3 (33 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (33 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (33 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (33 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (33 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (33 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (33 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (33 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (33 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 3 (33 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 209376553407347403635017813674301354500000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 18726981939396905367625982754392651397291000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 209376553407347403635017813674301354500000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 18727400692503720062433252790020000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((447209 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((19999552791 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((447209 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (33 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9364359934009983202943355585747000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(33 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 2304082761994063458011594496062340000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(33 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2304082761994063458011594496062340000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(33 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1152041048317682741989937953072251000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(33 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1074377351932189724329670397888369000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1074377351932189724329670397888369000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(33 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 2148754703864379448659340795776738000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(33 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (33 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1074377038349912224459194796639905000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(33 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 329174441194270643249813246883929107914571392000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7315562904465825444646840674733333784170857216000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 329174441194270643249813246883929107914571392000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(33 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 7973911786854366731146467168501192000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(33 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2580089061 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((28669910939 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2580089061 : ℚ)/62500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (33 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3986955911799402504301420232652333000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(33 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 15433459824179188384763164286869710000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 15433459824179188384763164286869710000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(33 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 30866919648358376769526328573739420000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(33 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (33 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15433459824179188384763164286869710000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 7973911786854366731146467168501192000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 7973911786854366731146467168501192000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (33 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3986955875054964226845046935848859000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(33 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1074377351932189724329670397888369000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1074377351932189724329670397888369000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 2 ⟨(33 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 2148754703864379448659340795776738000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(33 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (33 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1074377665514467224200145999136833000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 2304082761994063458011594496062340000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 2 ⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 2304082761994063458011594496062340000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (33 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1152041713676380716021656542990089000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 18727400692503720062433252790020000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 3 2 ⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 18727400692503720062433252790020000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 3 (33 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9363040758493736859489897204273000000000000000000000000 := by decide +kernel
  have hn : n3 3 (33 : Fin 88) = 27878936477584501742643000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![0,0],![0,2]] = ((5903644303359255771163 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![0,0],![1,1]] = ((86430592220140744228837 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![0,0],![2,0]] = ((5903644303359255771163 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![0,1],![0,1]] = ((39416439321 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![0,1],![1,0]] = ((39416439321 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![0,2],![0,0]] = ((5903644358297199776081 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![1,0],![0,1]] = ((39416439321 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![1,0],![1,0]] = ((39416439321 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![1,1],![0,0]] = ((86430604550202800223919 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88)
      ![![2,0],![0,0]] = ((5903644358297199776081 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (33 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (33 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_34_1 :
    (1386294361119887497824508000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (34 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(34 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(34 : Fin 88), complement (htotal3 3 (34 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (34 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (34 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (34 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (34 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (34 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (34 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(34 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 6626903386232146854143392710768000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 6626903386232146854143392710768000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(34 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 13253806772464293708286785421536000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(34 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (34 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6626917921895095274066651541078000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(34 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 320617729560508479511131808033374000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(34 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 320617729560508479511131808033374000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(34 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (34 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 160308867200448915150008096971824000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(34 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 286029733498204272749290703272545000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 286029733498204272749290703272545000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(34 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 572059466996408545498581406545090000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(34 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (34 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 286029696077365283724201261647478000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(34 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 572059466996408545498581406545090000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(34 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 572059466996408545498581406545090000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(34 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (34 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 286029770919043261774380144897612000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 160308864780254239755565904016687000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 160308864780254239755565904016687000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 1 ⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 320617729560508479511131808033374000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (34 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 160308862360059564361123711061550000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 13253806772464293708286785421536000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 1 ⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 13253806772464293708286785421536000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (34 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6626888850569198434220133880458000000000000000000000000 := by decide +kernel
  have hn : n3 3 (34 : Fin 88) = 905931003329381318718000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (34 : Fin 88)
      ![![0,0],![0,1]] = ((500000027933 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (34 : Fin 88)
      ![![0,0],![1,0]] = ((500000027933 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (34 : Fin 88)
      ![![0,1],![0,0]] = ((499999972067 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (34 : Fin 88)
      ![![1,0],![0,0]] = ((499999972067 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (34 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (34 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_34_2 :
    (1903214059018583136511991390569 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(34 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(34 : Fin 88), complement (htotal3 3 (34 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (34 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (34 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (34 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (34 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (34 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (34 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(34 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 13253806772464293708286785421536000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(34 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 13253806772464293708286785421536000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(34 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (34 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6626917921895095274066651541078000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(34 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 12079935921708633002595484805564744539422240000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 296457857717091213505940838422244510921155520000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 12079935921708633002595484805564744539422240000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(34 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 320617729560508479511131808033374000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(34 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((470963347 : ℚ)/12500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((5779036653 : ℚ)/6250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((470963347 : ℚ)/12500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (34 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 160308867200448915150008096971824000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(34 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 286029733498204272749290703272545000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 286029733498204272749290703272545000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(34 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 572059466996408545498581406545090000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(34 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (34 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 286029696077365283724201261647478000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(34 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 286029733498204272749290703272545000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 286029733498204272749290703272545000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(34 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 572059466996408545498581406545090000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(34 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (34 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 286029770919043261774380144897612000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 320617729560508479511131808033374000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 320617729560508479511131808033374000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (34 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 160308862360059564361123711061550000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 13253806772464293708286785421536000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 13253806772464293708286785421536000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (34 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6626888850569198434220133880458000000000000000000000000 := by decide +kernel
  have hn : n3 3 (34 : Fin 88) = 905931003329381318718000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![0,0],![0,2]] = ((3333569470230641123 : ℚ)/500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![0,0],![1,1]] = ((42733887818769358877 : ℚ)/250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![0,0],![2,0]] = ((3333569470230641123 : ℚ)/500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![0,1],![0,1]] = ((126292060851 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![0,1],![1,0]] = ((126292060851 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![0,2],![0,0]] = ((10417404909015398887 : ℚ)/1562500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![1,0],![0,1]] = ((126292060851 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![1,0],![1,0]] = ((126292060851 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![1,1],![0,0]] = ((133543428363640851113 : ℚ)/781250000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88)
      ![![2,0],![0,0]] = ((10417404909015398887 : ℚ)/1562500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (34 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (34 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1882658275868060309977927402536 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (31 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1718060822912193513620831254767 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (32 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1864164245230100361525207695287 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (32 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1892796802049574741255828867354 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (33 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1893039170324468033792469580543 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (33 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119887497824508000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (34 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1903214059018583136511991390569 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (34 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_3_31_2, L3C.mx_3_32_1, L3C.mx_3_32_2, L3C.mx_3_33_1, L3C.mx_3_33_2, L3C.mx_3_34_1, L3C.mx_3_34_2⟩
