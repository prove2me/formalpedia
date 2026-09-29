-- Prove2me | solution 1 for mme_released_recursive_level3_mixture154
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T19:21:10.323466+00:00
-- url     : https://prove2.me/submissions/478b3eec-d3d8-4991-a5bd-79e455466530

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

theorem mx_5_84_1 :
    (1846044377889923219475664753381 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(84 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(84 : Fin 88), complement (htotal3 5 (84 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (84 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (84 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (84 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (84 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (84 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (84 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 5 (84 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 5 (84 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(84 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4550171839077229906766123311904000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(84 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 4550171839077229906766123311904000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(84 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (84 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2275091795793288988966114610116000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 428035361023059751470472343756888000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 428035361023059751470472343756888000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 856070722046119502940944687513776000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 428035488390705545038886986198744000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 272969089009803680947151218495077664145998752000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5394347023194395167677801830490636671708002496000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 272969089009803680947151218495077664145998752000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 5940285201214002529572104267480792000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((11488046439 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((113511953561 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((11488046439 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 2970142456265832183819482409515160000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 84870009411007161764092460846764000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 84870009411007161764092460846764000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 169740018822014323528184921693528000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (84 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 84870213685791530225256597052904000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 169740018822014323528184921693528000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 169740018822014323528184921693528000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 84869805136222793302928324640624000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 2970142600607001264786052133740396000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2970142600607001264786052133740396000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 5940285201214002529572104267480792000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2970142744948170345752621857965632000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 17971606510767016584349111420624079212473808000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 820127509024585469772246464672527841575052384000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 17971606510767016584349111420624079212473808000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 1 ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 856070722046119502940944687513776000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((20993132983 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((479006867017 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((20993132983 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 428035233655413957902057701315032000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2275085919538614953383061655952000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2275085919538614953383061655952000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 1 ⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4550171839077229906766123311904000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (84 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2275080043283940917800008701788000000000000000000000000 := by decide +kernel
  have hn : n3 5 (84 : Fin 88) = 6970646113921213585948000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![0,0],![1,2]] = ((2500339151 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![0,0],![2,1]] = ((2500339151 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![0,1],![0,2]] = ((10434495934057088005739 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![0,1],![1,1]] = ((111440082756442911994261 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![0,1],![2,0]] = ((10434495934057088005739 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![0,2],![0,1]] = ((10434494598938651690871 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![0,2],![1,0]] = ((10434494598938651690871 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![1,0],![0,2]] = ((10434495934057088005739 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![1,0],![1,1]] = ((111440082756442911994261 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![1,0],![2,0]] = ((10434495934057088005739 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![1,1],![0,1]] = ((111440064602061348309129 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![1,1],![1,0]] = ((111440064602061348309129 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![1,2],![0,0]] = ((12501752679 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![2,0],![0,1]] = ((10434494598938651690871 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![2,0],![1,0]] = ((10434494598938651690871 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88)
      ![![2,1],![0,0]] = ((12501752679 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (84 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (84 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_84_2 :
    (1101619663630807021288934411468 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(84 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(84 : Fin 88), complement (htotal3 5 (84 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (84 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (84 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (84 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (84 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (84 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (84 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 5 (84 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 5 (84 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(84 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 4550171839077229906766123311904000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(84 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 4550171839077229906766123311904000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(84 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (84 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2275091795793288988966114610116000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 428035361023059751470472343756888000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 428035361023059751470472343756888000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 856070722046119502940944687513776000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 428035488390705545038886986198744000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 272969089009803680947151218495077664145998752000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5394347023194395167677801830490636671708002496000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 272969089009803680947151218495077664145998752000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 5940285201214002529572104267480792000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((11488046439 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((113511953561 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((11488046439 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 2970142456265832183819482409515160000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 84870009411007161764092460846764000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 84870009411007161764092460846764000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 169740018822014323528184921693528000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (84 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 84870213685791530225256597052904000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 84870009411007161764092460846764000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 84870009411007161764092460846764000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 169740018822014323528184921693528000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 84869805136222793302928324640624000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1637828942006727363002338697044771005907680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5937009543329989074846099590086702457988184640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1637828942006727363002338697044771005907680000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 5940285201214002529572104267480792000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((13785777 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((24986214223 : ℚ)/25000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((13785777 : ℚ)/50000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2970142744948170345752621857965632000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 428035361023059751470472343756888000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 428035361023059751470472343756888000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 2 ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 856070722046119502940944687513776000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 428035233655413957902057701315032000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4550171839077229906766123311904000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 2 ⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4550171839077229906766123311904000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (84 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2275080043283940917800008701788000000000000000000000000 := by decide +kernel
  have hn : n3 5 (84 : Fin 88) = 6970646113921213585948000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![0,0],![2,2]] = ((326380081 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![0,1],![1,2]] = ((4598797577 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![0,1],![2,1]] = ((4598797577 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![0,2],![0,2]] = ((67481029152142758343162640331 : ℚ)/6250000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![0,2],![1,1]] = ((61486825656950224747531837359669 : ℚ)/3125000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![0,2],![2,0]] = ((67481029152142758343162640331 : ℚ)/6250000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![1,0],![1,2]] = ((4598797577 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![1,0],![2,1]] = ((4598797577 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![1,1],![0,2]] = ((61486831568341904514481837359669 : ℚ)/3125000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![1,1],![1,1]] = ((1208499076986180727979643162640331 : ℚ)/1562500000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![1,1],![2,0]] = ((61486831568341904514481837359669 : ℚ)/3125000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![1,2],![0,1]] = ((36790369583 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![1,2],![1,0]] = ((36790369583 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![2,0],![0,2]] = ((67481029152142758343162640331 : ℚ)/6250000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![2,0],![1,1]] = ((61486825656950224747531837359669 : ℚ)/3125000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![2,0],![2,0]] = ((67481029152142758343162640331 : ℚ)/6250000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq16 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![2,1],![0,1]] = ((36790369583 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq17 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![2,1],![1,0]] = ((36790369583 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq18 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88)
      ![![2,2],![0,0]] = ((326381767 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (84 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (84 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_85_1 :
    (1386294361119863760213468000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (85 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(85 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(85 : Fin 88), complement (htotal3 5 (85 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (85 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (85 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (85 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (85 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (85 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (85 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(85 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 45586218158610851158002403391450000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(85 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 45586218158610851158002403391450000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(85 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (85 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22793358045239643249357652446140000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(85 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 594392574233719509902200377096305000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 594392574233719509902200377096305000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(85 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1188785148467439019804400754192610000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(85 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (85 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 594392254460627935211677758292260000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(85 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 2212406482617982946447596842415940000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(85 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2212406482617982946447596842415940000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(85 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (85 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1106202955009282981466700508681140000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1106203241308991473223798421207970000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1106203241308991473223798421207970000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2212406482617982946447596842415940000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1106203527608699964980896333734800000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1188785148467439019804400754192610000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1188785148467439019804400754192610000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 594392894006811084592722995900350000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 22793109079305425579001201695725000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 22793109079305425579001201695725000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 45586218158610851158002403391450000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22792860113371207908644750945310000000000000000000000000 := by decide +kernel
  have hn : n3 5 (85 : Fin 88) = 3446777849244032817410000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (85 : Fin 88)
      ![![0,0],![0,1]] = ((500000081943 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (85 : Fin 88)
      ![![0,0],![1,0]] = ((500000081943 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (85 : Fin 88)
      ![![0,1],![0,0]] = ((499999918057 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (85 : Fin 88)
      ![![1,0],![0,0]] = ((499999918057 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (85 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (85 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_85_2 :
    (1623496942217777415983185039025 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(85 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(85 : Fin 88), complement (htotal3 5 (85 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (85 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (85 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (85 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (85 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (85 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (85 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(85 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 45586218158610851158002403391450000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(85 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 45586218158610851158002403391450000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(85 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (85 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22793358045239643249357652446140000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(85 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 594392574233719509902200377096305000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 594392574233719509902200377096305000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(85 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1188785148467439019804400754192610000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(85 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (85 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 594392254460627935211677758292260000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(85 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1106203241308991473223798421207970000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1106203241308991473223798421207970000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(85 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2212406482617982946447596842415940000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(85 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (85 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1106202955009282981466700508681140000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 2212406482617982946447596842415940000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2212406482617982946447596842415940000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1106203527608699964980896333734800000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 56620461673790188221780741172086115881466610000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1075544225119858643360839271848437768237066780000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 56620461673790188221780741172086115881466610000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1188785148467439019804400754192610000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((47628843401 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((452371156599 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((47628843401 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 594392894006811084592722995900350000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 22793109079305425579001201695725000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 22793109079305425579001201695725000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 45586218158610851158002403391450000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22792860113371207908644750945310000000000000000000000000 := by decide +kernel
  have hn : n3 5 (85 : Fin 88) = 3446777849244032817410000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![0,1],![2,2]] = ((6612802191 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![0,2],![1,2]] = ((1642707903181329942827 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![0,2],![2,1]] = ((1642707903181329942827 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![1,0],![2,2]] = ((6612802191 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![1,1],![1,2]] = ((47696022238318670057173 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![1,1],![2,1]] = ((47696022238318670057173 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![1,2],![0,2]] = ((4106765339211192750993 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![1,2],![1,1]] = ((119239972095788807249007 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![1,2],![2,0]] = ((4106765339211192750993 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![2,0],![1,2]] = ((1642707903181329942827 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![2,0],![2,1]] = ((1642707903181329942827 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![2,1],![0,2]] = ((4106765339211192750993 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![2,1],![1,1]] = ((119239972095788807249007 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![2,1],![2,0]] = ((4106765339211192750993 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![2,2],![0,1]] = ((3306473327 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88)
      ![![2,2],![1,0]] = ((3306473327 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (85 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (85 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_86_1 :
    (1924720223628228819914413437566 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (40 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (40 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(86 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(86 : Fin 88), complement (htotal3 5 (86 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (86 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (86 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (86 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (86 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (86 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (86 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(86 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 51078874902029947148967074311672000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(86 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 51078874902029947148967074311672000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(86 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (86 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25547611166613783918879708204876000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(86 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1242348526880494344614846400676104000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1242348526880494344614846400676104000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(86 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2484697053760988689229692801352208000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(86 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (86 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1242339614876179459857591201809764000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(86 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 63758429446384959258605151246885144646400720000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1212747197084782958572129821842349710707198560000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 63758429446384959258605151246885144646400720000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(86 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 1340264055977552877089340124336120000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(86 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((23785771603 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((226214228397 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((23785771603 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (86 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 670135386127802491381580186627772000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(86 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1340264055977552877089340124336120000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(86 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1340264055977552877089340124336120000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(86 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (86 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 670128669849750385707759937708348000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(86 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1242348526880494344614846400676104000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1242348526880494344614846400676104000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(86 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2484697053760988689229692801352208000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(86 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (86 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1242357438884809229372101599542444000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1076104011990831016408395264502406703124016000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 48926666878048285116150283782667186593751968000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1076104011990831016408395264502406703124016000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 51078874902029947148967074311672000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((10533748189 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((239466251811 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10533748189 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25531263735416163230087366106796000000000000000000000000 := by decide +kernel
  have hn : n3 5 (86 : Fin 88) = 3876039984640571513468000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![0,0],![0,2]] = ((1045438105176757488239 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![0,0],![1,1]] = ((10172136464698242511761 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![0,0],![2,0]] = ((1045438105176757488239 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![0,1],![0,1]] = ((160260024639 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![0,1],![1,0]] = ((160260024639 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![0,2],![0,0]] = ((209087460460795347061 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![1,0],![0,1]] = ((160260024639 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![1,0],![1,0]] = ((160260024639 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![1,1],![0,0]] = ((2034396393614204652939 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88)
      ![![2,0],![0,0]] = ((209087460460795347061 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (86 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (86 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_86_2 :
    (1623474175858529427795217232330 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(86 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(86 : Fin 88), complement (htotal3 5 (86 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (86 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (86 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (86 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (86 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (86 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (86 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(86 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 51078874902029947148967074311672000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(86 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 51078874902029947148967074311672000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(86 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (86 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25547611166613783918879708204876000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(86 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1242348526880494344614846400676104000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1242348526880494344614846400676104000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(86 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2484697053760988689229692801352208000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(86 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (86 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1242339614876179459857591201809764000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(86 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 63758429446384959258605151246885144646400720000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1212747197084782958572129821842349710707198560000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 63758429446384959258605151246885144646400720000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(86 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 1340264055977552877089340124336120000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(86 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((23785771603 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((226214228397 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((23785771603 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (86 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 670135386127802491381580186627772000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(86 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 670132027988776438544670062168060000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 670132027988776438544670062168060000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(86 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1340264055977552877089340124336120000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(86 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (86 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 670128669849750385707759937708348000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(86 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 2484697053760988689229692801352208000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(86 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2484697053760988689229692801352208000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(86 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (86 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1242357438884809229372101599542444000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 25539437451014973574483537155836000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 25539437451014973574483537155836000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 51078874902029947148967074311672000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25531263735416163230087366106796000000000000000000000000 := by decide +kernel
  have hn : n3 5 (86 : Fin 88) = 3876039984640571513468000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![0,1],![2,2]] = ((6586945397 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![0,2],![1,2]] = ((4112363985069216305187 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![0,2],![2,1]] = ((4112363985069216305187 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![1,0],![2,2]] = ((6586945397 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![1,1],![1,2]] = ((119241163880430783694813 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![1,1],![2,1]] = ((119241163880430783694813 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![1,2],![0,2]] = ((4112322769845327318083 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![1,2],![1,1]] = ((119239622276154672681917 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![1,2],![2,0]] = ((4112322769845327318083 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![2,0],![1,2]] = ((4112363985069216305187 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![2,0],![2,1]] = ((4112363985069216305187 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![2,1],![0,2]] = ((4112322769845327318083 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![2,1],![1,1]] = ((119239622276154672681917 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![2,1],![2,0]] = ((4112322769845327318083 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![2,2],![0,1]] = ((6591162957 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88)
      ![![2,2],![1,0]] = ((6591162957 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (86 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (86 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_87_1 :
    (1386294361089131083042080000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (87 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(87 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(87 : Fin 88), complement (htotal3 5 (87 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (87 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (87 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (87 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (87 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (87 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (87 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(87 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25145925956467430360394047524920000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(87 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 25145925956467430360394047524920000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(87 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (87 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12572658975862170509613310660920000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(87 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42229679920736883559802976237540000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42229679920736883559802976237540000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(87 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 84459359841473767119605952475080000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(87 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (87 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42229679860837594871228111814720000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(87 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84459359841473767119605952475080000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(87 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 84459359841473767119605952475080000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(87 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (87 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42229679980636172248377840660360000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(87 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12572962978233715180197023762460000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12572962978233715180197023762460000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(87 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 25145925956467430360394047524920000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(87 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (87 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12573266980605259850780736864000000000000000000000000000 := by decide +kernel
  have hn : n3 5 (87 : Fin 88) = 109605285797941197480000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (87 : Fin 88)
      ![![0,0],![0,1]] = ((62499653367 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (87 : Fin 88)
      ![![0,0],![1,0]] = ((62499653367 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (87 : Fin 88)
      ![![0,1],![0,0]] = ((62500346633 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (87 : Fin 88)
      ![![1,0],![0,0]] = ((62500346633 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (87 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (87 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1846044377889923219475664753381 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (84 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1101619663630807021288934411468 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (84 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119863760213468000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (85 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1623496942217777415983185039025 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (85 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1924720223628228819914413437566 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (86 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (40 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (40 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1623474175858529427795217232330 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (86 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361089131083042080000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (87 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_5_84_1, L3C.mx_5_84_2, L3C.mx_5_85_1, L3C.mx_5_85_2, L3C.mx_5_86_1, L3C.mx_5_86_2, L3C.mx_5_87_1⟩
