-- Prove2me | solution 1 for mme_released_recursive_level3_mixture85
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T18:45:37.339572+00:00
-- url     : https://prove2.me/submissions/85b3364b-7887-4fe7-a0d1-220a32f34fd9

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

theorem mx_3_24_2 :
    (1659058379260974332265392230135 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(24 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(24 : Fin 88), complement (htotal3 3 (24 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (24 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (24 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (24 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (24 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (24 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (24 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 46354599561117021802960227282255000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 46354599561117021802960227282255000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (24 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23177285766615615563812983482955000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 992421009140255861847845523002627500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 992421009140255861847845523002627500000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1984842018280511723695691046005255000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (24 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 992421027757858453127806806393405000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 63320556285473118833945841810978739709992570000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 988887967429047814668457043090532520580014860000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 63320556285473118833945841810978739709992570000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 1115529079999994052336348726712490000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((56762801993 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((443237198007 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((56762801993 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (24 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 557764534710351128096406440195610000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 557764539999997026168174363356245000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 557764539999997026168174363356245000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1115529079999994052336348726712490000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (24 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 557764545289642924239942286516880000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(24 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 1984842018280511723695691046005255000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(24 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 1984842018280511723695691046005255000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(24 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (24 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 992420990522653270567884239611850000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(24 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 23177299780558510901480113641127500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 23177299780558510901480113641127500000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(24 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 46354599561117021802960227282255000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(24 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (24 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23177313794501406239147243799300000000000000000000000000 := by decide +kernel
  have hn : n3 3 (24 : Fin 88) = 3146725697841622797835000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![0,1],![2,2]] = ((368276679 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![0,2],![1,2]] = ((5030670112777482329919 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![0,2],![2,1]] = ((5030670112777482329919 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![1,0],![2,2]] = ((368276679 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![1,1],![1,2]] = ((118127945706222517670081 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![1,1],![2,1]] = ((118127945706222517670081 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![1,2],![0,2]] = ((628833776024469060019 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![1,2],![1,1]] = ((14765993676194280939981 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![1,2],![2,0]] = ((628833776024469060019 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![2,0],![1,2]] = ((5030670112777482329919 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![2,0],![2,1]] = ((5030670112777482329919 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![2,1],![0,2]] = ((628833776024469060019 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![2,1],![1,1]] = ((14765993676194280939981 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![2,1],![2,0]] = ((628833776024469060019 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![2,2],![0,1]] = ((7365524673 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88)
      ![![2,2],![1,0]] = ((7365524673 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (24 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (24 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_25_1 :
    (1386294361119890042738460000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (25 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(25 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(25 : Fin 88), complement (htotal3 3 (25 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (25 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (25 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (25 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (25 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (25 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (25 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(25 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 41782261716615005710011238432065000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(25 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 41782261716615005710011238432065000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(25 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (25 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20891213421089159730900167699535000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 502596110670967755240553421645850000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 502596110670967755240553421645850000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1005192221341935510481106843291700000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (25 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 502596086459066640042684987468105000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1793797676415562875123881918276235000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1793797676415562875123881918276235000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (25 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 896898765525205351337012785648185000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(25 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 896898838207781437561940959138117500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 896898838207781437561940959138117500000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(25 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 1793797676415562875123881918276235000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(25 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 896898910890357523786869132628050000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1005192221341935510481106843291700000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 1 ⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1005192221341935510481106843291700000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 502596134882868870438421855823595000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(25 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 20891130858307502855005619216032500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 20891130858307502855005619216032500000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 1 ⟨(25 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 41782261716615005710011238432065000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(25 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20891048295525845979111070732530000000000000000000000000 := by decide +kernel
  have hn : n3 3 (25 : Fin 88) = 2840772159474113391315000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (25 : Fin 88)
      ![![0,0],![0,1]] = ((500000012001 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (25 : Fin 88)
      ![![0,0],![1,0]] = ((500000012001 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (25 : Fin 88)
      ![![0,1],![0,0]] = ((499999987999 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (25 : Fin 88)
      ![![1,0],![0,0]] = ((499999987999 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (25 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (25 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_25_2 :
    (1658752834728229664636028171151 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(25 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(25 : Fin 88), complement (htotal3 3 (25 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (25 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (25 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (25 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (25 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (25 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (25 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(25 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 41782261716615005710011238432065000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(25 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 41782261716615005710011238432065000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(25 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (25 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20891213421089159730900167699535000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 502596110670967755240553421645850000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 502596110670967755240553421645850000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1005192221341935510481106843291700000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (25 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 502596086459066640042684987468105000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 896898838207781437561940959138117500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 896898838207781437561940959138117500000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1793797676415562875123881918276235000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (25 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 896898765525205351337012785648185000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(25 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 1793797676415562875123881918276235000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(25 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 1793797676415562875123881918276235000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(25 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 896898910890357523786869132628050000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 57086535949677583195750130035085363760577500000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 891019149442580344089606583221529272478845000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 57086535949677583195750130035085363760577500000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1005192221341935510481106843291700000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2271666443 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((17728333557 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2271666443 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 502596134882868870438421855823595000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(25 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 20891130858307502855005619216032500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 20891130858307502855005619216032500000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(25 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 41782261716615005710011238432065000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(25 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20891048295525845979111070732530000000000000000000000000 := by decide +kernel
  have hn : n3 3 (25 : Fin 88) = 2840772159474113391315000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![0,1],![2,2]] = ((3677001731 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![0,2],![1,2]] = ((401908604386728889059 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![0,2],![2,1]] = ((401908604386728889059 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![1,0],![2,2]] = ((3677001731 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![1,1],![1,2]] = ((9451011427273271110941 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![1,1],![2,1]] = ((9451011427273271110941 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![1,2],![0,2]] = ((401908565663902701681 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![1,2],![1,1]] = ((9451010101656097298319 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![1,2],![2,0]] = ((401908565663902701681 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![2,0],![1,2]] = ((401908604386728889059 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![2,0],![2,1]] = ((401908604386728889059 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![2,1],![0,2]] = ((401908565663902701681 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![2,1],![1,1]] = ((9451010101656097298319 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![2,1],![2,0]] = ((401908565663902701681 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![2,2],![0,1]] = ((7354061589 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88)
      ![![2,2],![1,0]] = ((7354061589 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (25 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (25 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_26_1 :
    (1386294361119890618804188000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (26 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(26 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(26 : Fin 88), complement (htotal3 3 (26 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (26 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (26 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (26 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (26 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(26 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 26503707170042808777960447787470000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(26 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 26503707170042808777960447787470000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(26 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (26 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13251853575608672659918469190840000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(26 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42444783865048150066019776106265000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42444783865048150066019776106265000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(26 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 84889567730096300132039552212530000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(26 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (26 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42444783865326633253270123878540000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(26 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84889567730096300132039552212530000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(26 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 84889567730096300132039552212530000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(26 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (26 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42444783864769666878769428333990000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(26 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 13251853585021404388980223893735000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 13251853585021404388980223893735000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(26 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 26503707170042808777960447787470000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(26 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13251853594434136118041978596630000000000000000000000000 := by decide +kernel
  have hn : n3 3 (26 : Fin 88) = 111393274900139108910000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (26 : Fin 88)
      ![![0,0],![0,1]] = ((499999999913 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (26 : Fin 88)
      ![![0,0],![1,0]] = ((499999999913 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (26 : Fin 88)
      ![![0,1],![0,0]] = ((500000000087 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (26 : Fin 88)
      ![![1,0],![0,0]] = ((500000000087 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (26 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (26 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_26_2 :
    (1818580917195352610640342495053 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(26 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(26 : Fin 88), complement (htotal3 3 (26 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,2],![2,2]] + g ![![1,1],![2,2]] + g ![![1,2],![1,2]] + g ![![1,2],![2,1]] + g ![![2,0],![2,2]] + g ![![2,1],![1,2]] + g ![![2,1],![2,1]] + g ![![2,2],![0,2]] + g ![![2,2],![1,1]] + g ![![2,2],![2,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (26 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (26 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (26 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (26 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(26 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 26503707170042808777960447787470000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(26 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 26503707170042808777960447787470000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(26 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (26 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13251853575608672659918469190840000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(26 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42444783865048150066019776106265000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42444783865048150066019776106265000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(26 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 84889567730096300132039552212530000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(26 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (26 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42444783865326633253270123878540000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(26 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42444783865048150066019776106265000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42444783865048150066019776106265000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(26 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 84889567730096300132039552212530000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(26 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (26 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42444783864769666878769428333990000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(26 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 558617075060654793771806571257972299166880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25386473019921499190416834644954055401666240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 558617075060654793771806571257972299166880000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(26 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 26503707170042808777960447787470000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(26 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((1317308819 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((29932691181 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1317308819 : ℚ)/62500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13251853594434136118041978596630000000000000000000000000 := by decide +kernel
  have hn : n3 3 (26 : Fin 88) = 111393274900139108910000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![0,2],![2,2]] = ((156713083655134881367 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![1,1],![2,2]] = ((3560929881751115118633 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![1,2],![1,2]] = ((762070850383 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![1,2],![2,1]] = ((762070850383 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![2,0],![2,2]] = ((156713083655134881367 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![2,1],![1,2]] = ((762070850383 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![2,1],![2,1]] = ((762070850383 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![2,2],![0,2]] = ((39178270858127422739 : ℚ)/15625000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![2,2],![1,1]] = ((890232469173122577261 : ℚ)/7812500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88)
      ![![2,2],![2,0]] = ((39178270858127422739 : ℚ)/15625000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (26 : Fin 88)) _ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (26 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_27_1 :
    (1765393185179656856587129718536 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(27 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(27 : Fin 88), complement (htotal3 3 (27 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,2],![2,2]] + g ![![1,1],![2,2]] + g ![![1,2],![1,2]] + g ![![1,2],![2,1]] + g ![![2,0],![2,2]] + g ![![2,1],![1,2]] + g ![![2,1],![2,1]] + g ![![2,2],![0,2]] + g ![![2,2],![1,1]] + g ![![2,2],![2,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (27 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (27 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (27 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (27 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42313090096359027694547321041600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42313090096359027694547321041600000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84626180192718055389094642083200000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (27 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42313077340029773087632620676800000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25069826743568704210905357916800000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25069826743568704210905357916800000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12534904604550389736605991447600000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(27 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 18005851522379863287990133405867430400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25069790731865659451178781936533188265139200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18005851522379863287990133405867430400000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(27 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25069826743568704210905357916800000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(27 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((179557 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((124999820443 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((179557 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (27 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12534922139018314474299366469200000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42313090096359027694547321041600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42313090096359027694547321041600000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84626180192718055389094642083200000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (27 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42313102852688282301462021406400000000000000000000000000 := by decide +kernel
  have hn : n3 3 (27 : Fin 88) = 109696006936286759600000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![0,2],![2,2]] = ((20517911976713739 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![1,1],![2,2]] = ((14283683247963023286261 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![1,2],![1,2]] = ((96432612449 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![1,2],![2,1]] = ((96432612449 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![2,0],![2,2]] = ((20517911976713739 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![2,1],![1,2]] = ((96432612449 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![2,1],![2,1]] = ((96432612449 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![2,2],![0,2]] = ((20517883275245517 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![2,2],![1,1]] = ((14283663267241724754483 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88)
      ![![2,2],![2,0]] = ((20517883275245517 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (27 : Fin 88)) _ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (27 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_27_2 :
    (1386294361119885329181564000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (27 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(27 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(27 : Fin 88), complement (htotal3 3 (27 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (27 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (27 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (27 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (27 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42313090096359027694547321041600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42313090096359027694547321041600000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84626180192718055389094642083200000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (27 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42313077340029773087632620676800000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25069826743568704210905357916800000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25069826743568704210905357916800000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12534904604550389736605991447600000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(27 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12534913371784352105452678958400000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12534913371784352105452678958400000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(27 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25069826743568704210905357916800000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(27 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (27 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12534922139018314474299366469200000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84626180192718055389094642083200000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84626180192718055389094642083200000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (27 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42313102852688282301462021406400000000000000000000000000 := by decide +kernel
  have hn : n3 3 (27 : Fin 88) = 109696006936286759600000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (27 : Fin 88)
      ![![0,0],![0,1]] = ((100000007273 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (27 : Fin 88)
      ![![0,0],![1,0]] = ((100000007273 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (27 : Fin 88)
      ![![0,1],![0,0]] = ((99999992727 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (27 : Fin 88)
      ![![1,0],![0,0]] = ((99999992727 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (27 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (27 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1659058379260974332265392230135 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (24 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119890042738460000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (25 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1658752834728229664636028171151 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (25 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119890618804188000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (26 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1818580917195352610640342495053 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (26 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1765393185179656856587129718536 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (27 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119885329181564000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (27 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_3_24_2, L3C.mx_3_25_1, L3C.mx_3_25_2, L3C.mx_3_26_1, L3C.mx_3_26_2, L3C.mx_3_27_1, L3C.mx_3_27_2⟩
