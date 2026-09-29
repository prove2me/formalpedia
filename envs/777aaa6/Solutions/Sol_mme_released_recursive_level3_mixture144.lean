-- Prove2me | solution 1 for mme_released_recursive_level3_mixture144
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T19:57:22.426427+00:00
-- url     : https://prove2.me/submissions/07a63f4e-bd63-4350-85d9-4d857622aa5c

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

theorem mx_5_49_1 :
    (1706941973599197420490753944400 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(49 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(49 : Fin 88), complement (htotal3 5 (49 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (49 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (49 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (49 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (49 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (49 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (49 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 13575597976818876634219548580159469544947328000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 333249184147116852805186642299137060910105344000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 13575597976818876634219548580159469544947328000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 360400380100754606073625739459456000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((37668101163 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((462331898837 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((37668101163 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 180200139560832773964335070115136000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 321246208765064853672715299311104000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 321246208765064853672715299311104000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 642492417530129707345430598622208000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (49 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 321246374950231205996364811218368000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 14918445546805437812943661918336000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 14918445546805437812943661918336000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (49 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7459043127682675557875359008704000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(49 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 7459222773402718906471830959168000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 7459222773402718906471830959168000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(49 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 14918445546805437812943661918336000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(49 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7459402419122762255068302909632000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(49 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 13541548918015420692390105963464042049216512000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 615409319694098865960650386695279915901566976000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 13541548918015420692390105963464042049216512000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(49 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 642492417530129707345430598622208000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(49 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2634573683 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((59865426317 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2634573683 : ℚ)/125000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (49 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 321246042579898501349065787403840000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 180200190050377303036812869729728000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 180200190050377303036812869729728000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 360400380100754606073625739459456000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (49 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 180200240539921832109290669344320000000000000000000000000 := by decide +kernel
  have hn : n3 5 (49 : Fin 88) = 1017811243177689751232000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![0,1],![2,2]] = ((7328866201 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![0,2],![1,2]] = ((13321299144450788035629 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![0,2],![2,1]] = ((13321299144450788035629 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![1,0],![2,2]] = ((7328866201 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![1,1],![1,2]] = ((233014249564549211964371 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![1,1],![2,1]] = ((233014249564549211964371 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![1,2],![0,2]] = ((13321309764223036446241 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![1,2],![1,1]] = ((233014451827776963553759 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![1,2],![2,0]] = ((13321309764223036446241 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![2,0],![1,2]] = ((13321299144450788035629 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![2,0],![2,1]] = ((13321299144450788035629 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![2,1],![0,2]] = ((13321309764223036446241 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![2,1],![1,1]] = ((233014451827776963553759 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![2,1],![2,0]] = ((13321309764223036446241 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![2,2],![0,1]] = ((7328513197 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88)
      ![![2,2],![1,0]] = ((7328513197 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (49 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (49 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_49_2 :
    (1903221507207457138967820555797 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(49 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(49 : Fin 88), complement (htotal3 5 (49 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (49 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (49 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (49 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (49 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (49 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (49 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 13575597976818876634219548580159469544947328000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 333249184147116852805186642299137060910105344000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 13575597976818876634219548580159469544947328000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 360400380100754606073625739459456000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((37668101163 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((462331898837 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((37668101163 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 180200139560832773964335070115136000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 321246208765064853672715299311104000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 321246208765064853672715299311104000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 642492417530129707345430598622208000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (49 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 321246374950231205996364811218368000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 14918445546805437812943661918336000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 14918445546805437812943661918336000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (49 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7459043127682675557875359008704000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(49 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 14918445546805437812943661918336000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(49 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 14918445546805437812943661918336000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(49 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7459402419122762255068302909632000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(49 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 321246208765064853672715299311104000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 321246208765064853672715299311104000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(49 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 642492417530129707345430598622208000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(49 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (49 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 321246042579898501349065787403840000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 360400380100754606073625739459456000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 360400380100754606073625739459456000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (49 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 180200240539921832109290669344320000000000000000000000000 := by decide +kernel
  have hn : n3 5 (49 : Fin 88) = 1017811243177689751232000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![0,0],![0,2]] = ((1333803479918858249301 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![0,0],![1,1]] = ((17103729503281141750699 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![0,0],![2,0]] = ((1333803479918858249301 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![0,1],![0,1]] = ((39453067909 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![0,1],![1,0]] = ((39453067909 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![0,2],![0,0]] = ((6669013662466638662949 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![1,0],![0,1]] = ((39453067909 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![1,0],![1,0]] = ((39453067909 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![1,1],![0,0]] = ((85518778149533361337051 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88)
      ![![2,0],![0,0]] = ((6669013662466638662949 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (49 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (49 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_50_1 :
    (1870916440767259495935946810312 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(50 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(50 : Fin 88), complement (htotal3 5 (50 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (50 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (50 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (50 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (50 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (50 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (50 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 5 (50 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 5 (50 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 5 (50 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 5 (50 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 52747177048242544542724414618050000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 52747177048242544542724414618050000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 105494354096485089085448829236100000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (50 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 52747118467594329490342445324790000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 38852010679263338680346654285235741376787250000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 643202569480497142598020249191418517246425500000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 38852010679263338680346654285235741376787250000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 720906590839023819958713557761890000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2155730641 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((17844269359 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2155730641 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (50 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 360453159104354587854420330400920000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 775063121719317348615084770327370000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 775063121719317348615084770327370000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (50 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 387531292202837610536028730306860000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10178575137127492763295295069893135000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10178575137127492763295295069893135000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 20357150274254985526590590139786270000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (50 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10178575510846727763143589011871150000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 203084230403257236534435378269495394822657030000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10071899487902932861891291946349379210354685940000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 203084230403257236534435378269495394822657030000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 10478067948709447334960162702888370000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((19381839419 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((480618160581 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((19381839419 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (50 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5239033905021315273418914984132810000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 10478067948709447334960162702888370000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10478067948709447334960162702888370000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (50 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5239034043688132061541247718755560000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10178575137127492763295295069893135000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10178575137127492763295295069893135000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 20357150274254985526590590139786270000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10178574763408257763447001127915120000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39383461345071773139132529245110831600894010000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 696296199029173802336819711837148336798211980000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39383461345071773139132529245110831600894010000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 775063121719317348615084770327370000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((50813230873 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((449186769127 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((50813230873 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (50 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 387531829516479738079056040020510000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 720906590839023819958713557761890000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 720906590839023819958713557761890000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 5 (50 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 360453431734669232104293227360970000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(50 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 52747177048242544542724414618050000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 52747177048242544542724414618050000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 5 1 ⟨(50 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 105494354096485089085448829236100000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(50 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 5 (50 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 52747235628890759595106383911310000000000000000000000000 := by decide +kernel
  have hn : n3 5 (50 : Fin 88) = 32436682289619259119210000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![0,0],![0,2]] = ((4336443690413079725427 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![0,0],![1,1]] = ((87951335839086920274573 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![0,0],![2,0]] = ((4336443690413079725427 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![0,1],![0,1]] = ((630848877997 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![0,1],![1,0]] = ((630848877997 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![0,2],![0,0]] = ((2168221998151992340161 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![1,0],![0,1]] = ((630848877997 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![1,0],![1,0]] = ((630848877997 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![1,1],![0,0]] = ((43975668737848007659839 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88)
      ![![2,0],![0,0]] = ((2168221998151992340161 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (50 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (50 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_50_2 :
    (1702298671782622619921951347425 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(50 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(50 : Fin 88), complement (htotal3 5 (50 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (50 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (50 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (50 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (50 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (50 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (50 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 5 (50 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 5 (50 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 5 (50 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 5 (50 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 52747177048242544542724414618050000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 52747177048242544542724414618050000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 105494354096485089085448829236100000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (50 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 52747118467594329490342445324790000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 38852010679263338680346654285235741376787250000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 643202569480497142598020249191418517246425500000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 38852010679263338680346654285235741376787250000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 720906590839023819958713557761890000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2155730641 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((17844269359 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2155730641 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (50 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 360453159104354587854420330400920000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 387531560859658674307542385163685000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 387531560859658674307542385163685000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 775063121719317348615084770327370000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (50 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 387531292202837610536028730306860000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 20357150274254985526590590139786270000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 20357150274254985526590590139786270000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (50 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10178575510846727763143589011871150000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 5239033974354723667480081351444185000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 5239033974354723667480081351444185000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 10478067948709447334960162702888370000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (50 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5239033905021315273418914984132810000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 596320012391480502535423053491809248364695750000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9285427923926486329889316595904751503270608500000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 596320012391480502535423053491809248364695750000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10478067948709447334960162702888370000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2276450259 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((17723549741 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2276450259 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (50 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5239034043688132061541247718755560000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10178575137127492763295295069893135000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10178575137127492763295295069893135000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 20357150274254985526590590139786270000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10178574763408257763447001127915120000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 775063121719317348615084770327370000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 775063121719317348615084770327370000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (50 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 387531829516479738079056040020510000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 360453295419511909979356778880945000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 360453295419511909979356778880945000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 720906590839023819958713557761890000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 5 (50 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 360453431734669232104293227360970000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(50 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 105494354096485089085448829236100000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 5 2 ⟨(50 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 105494354096485089085448829236100000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(50 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 5 (50 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 52747235628890759595106383911310000000000000000000000000 := by decide +kernel
  have hn : n3 5 (50 : Fin 88) = 32436682289619259119210000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![0,0],![1,2]] = ((6786746271 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![0,0],![2,1]] = ((6786746271 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![0,1],![0,2]] = ((97909524809085333209 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![0,1],![1,1]] = ((2334223015640914666791 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![0,1],![2,0]] = ((97909524809085333209 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![0,2],![0,1]] = ((48954761356156269057 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![0,2],![1,0]] = ((48954761356156269057 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![1,0],![0,2]] = ((97909524809085333209 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![1,0],![1,1]] = ((2334223015640914666791 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![1,0],![2,0]] = ((97909524809085333209 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![1,1],![0,1]] = ((1167111556151343730943 : ℚ)/5000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![1,1],![1,0]] = ((1167111556151343730943 : ℚ)/5000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![1,2],![0,0]] = ((2714694473 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![2,0],![0,1]] = ((48954761356156269057 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![2,0],![1,0]] = ((48954761356156269057 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88)
      ![![2,1],![0,0]] = ((2714694473 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (50 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (50 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_51_1 :
    (1386294361119889819980768000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (51 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(51 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(51 : Fin 88), complement (htotal3 5 (51 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (51 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (51 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (51 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (51 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (51 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (51 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 5 (51 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 5 (51 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 498763013731396077323731987600000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 498763013731396077323731987600000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (51 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 249381799859334708995000895400000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 9287180427607267081874347725020000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9287180427607267081874347725020000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 18574360855214534163748695450040000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (51 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 9287191669696002533959277811280000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 94921297300518680067710907911680000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 94921297300518680067710907911680000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (51 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 47460638304499822027197548404080000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(51 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 328520732402548135505608332325340000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 328520732402548135505608332325340000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(51 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 657041464805096271011216664650680000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(51 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 328520722003972659309693006403160000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 657041464805096271011216664650680000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 657041464805096271011216664650680000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 328520742801123611701523658247520000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(51 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 47460648650259340033855453955840000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 47460648650259340033855453955840000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(51 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 94921297300518680067710907911680000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(51 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 47460658996018858040513359507600000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 18574360855214534163748695450040000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 1 ⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 18574360855214534163748695450040000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (51 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9287169185518531629789417638760000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(51 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 249381506865698038661865993800000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 249381506865698038661865993800000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 1 ⟨(51 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 498763013731396077323731987600000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(51 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (51 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 249381213872061368328731092200000000000000000000000000 := by decide +kernel
  have hn : n3 5 (51 : Fin 88) = 771035885974560881320000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (51 : Fin 88)
      ![![0,0],![0,1]] = ((124999996467 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (51 : Fin 88)
      ![![0,0],![1,0]] = ((124999996467 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (51 : Fin 88)
      ![![0,1],![0,0]] = ((125000003533 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (51 : Fin 88)
      ![![1,0],![0,0]] = ((125000003533 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (51 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (51 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_51_2 :
    (1101761158916581556090279376349 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(51 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(51 : Fin 88), complement (htotal3 5 (51 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (51 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (51 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (51 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (51 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (51 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (51 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 5 (51 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 5 (51 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 498763013731396077323731987600000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 498763013731396077323731987600000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (51 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 249381799859334708995000895400000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 9287180427607267081874347725020000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 9287180427607267081874347725020000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 18574360855214534163748695450040000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (51 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 9287191669696002533959277811280000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 47460648650259340033855453955840000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 47460648650259340033855453955840000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 94921297300518680067710907911680000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (51 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 47460638304499822027197548404080000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(51 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 181453015806084792678730984990668150650200000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 656678558773484101425859202680698663698699600000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 181453015806084792678730984990668150650200000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(51 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 657041464805096271011216664650680000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(51 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((55233353 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((99944766647 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((55233353 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 328520722003972659309693006403160000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 30198259203714184730804443203802742435916560000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 596644946397667901549607778243074515128166880000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 30198259203714184730804443203802742435916560000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 657041464805096271011216664650680000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((22980482071 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((227019517929 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((22980482071 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 328520742801123611701523658247520000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(51 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 47460648650259340033855453955840000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 47460648650259340033855453955840000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(51 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 94921297300518680067710907911680000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(51 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 47460658996018858040513359507600000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 9287180427607267081874347725020000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9287180427607267081874347725020000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 2 ⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 18574360855214534163748695450040000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (51 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9287169185518531629789417638760000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(51 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 498763013731396077323731987600000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 2 ⟨(51 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 498763013731396077323731987600000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(51 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (51 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 249381213872061368328731092200000000000000000000000000 := by decide +kernel
  have hn : n3 5 (51 : Fin 88) = 771035885974560881320000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![0,0],![2,2]] = ((64687317 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![0,1],![1,2]] = ((73599464323 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![0,1],![2,1]] = ((73599464323 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![0,2],![0,2]] = ((1081630012898826284251377977237 : ℚ)/100000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![0,2],![1,1]] = ((983947527587044185581098622022763 : ℚ)/50000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![0,2],![2,0]] = ((1081630012898826284251377977237 : ℚ)/100000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![1,0],![1,2]] = ((73599464323 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![1,0],![2,1]] = ((73599464323 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![1,1],![0,2]] = ((983947465974242203090048622022763 : ℚ)/50000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![1,1],![1,1]] = ((19334878253900814785044601377977237 : ℚ)/25000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![1,1],![2,0]] = ((983947465974242203090048622022763 : ℚ)/50000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![1,2],![0,1]] = ((9199933331 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![1,2],![1,0]] = ((9199933331 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![2,0],![0,2]] = ((1081630012898826284251377977237 : ℚ)/100000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![2,0],![1,1]] = ((983947527587044185581098622022763 : ℚ)/50000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![2,0],![2,0]] = ((1081630012898826284251377977237 : ℚ)/100000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq16 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![2,1],![0,1]] = ((9199933331 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq17 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![2,1],![1,0]] = ((9199933331 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq18 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88)
      ![![2,2],![0,0]] = ((64687469 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (51 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (51 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_52_1 :
    (1925687572790809583452955339229 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(52 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(52 : Fin 88), complement (htotal3 5 (52 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (52 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (52 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (52 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (52 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (52 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (52 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 5 (52 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 5 (52 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 5 (52 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 22427966403115820596943672672250000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 22427966403115820596943672672250000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11215249955971850998860015708000000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1273318214037064922699173010667375000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1273318214037064922699173010667375000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2546636428074129845398346021334750000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1273317551185565219536974734959500000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 539206272592066582799127196394358228211452000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9215474222020517792178795426172283543577096000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 539206272592066582799127196394358228211452000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 10293886767204650957777049818961000000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((13095303183 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((111904696817 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((13095303183 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5146943387671373925191640036619500000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 2572855676873132726168013794438250000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2572855676873132726168013794438250000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1286427169867352032788983054928000000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(52 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 19642197008885618297809646692593750000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 19642197008885618297809646692593750000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(52 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 39284394017771236595619293385187500000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(52 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19642197008885618297809646692593750000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(52 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 54258229339688611517003639243978347587629250000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2464339218193755503134006515950293304824741500000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 54258229339688611517003639243978347587629250000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(52 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 2572855676873132726168013794438250000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(52 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((21088718589 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((478911281411 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((21088718589 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1286428507005780693379030739510250000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 10293886767204650957777049818961000000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 1 ⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10293886767204650957777049818961000000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5146943379533277032585409782341500000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(52 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1273318214037064922699173010667375000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1273318214037064922699173010667375000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 1 ⟨(52 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 2546636428074129845398346021334750000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(52 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1273318876888564625861371286375250000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(52 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 708510023031583464318005501079234673278750000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 21010946357052653668307661670091530653442500000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 708510023031583464318005501079234673278750000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 5 1 ⟨(52 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 22427966403115820596943672672250000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(52 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((6318094207 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((93681905793 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((6318094207 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 5 (52 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11212716447143969598083656964250000000000000000000000000 := by decide +kernel
  have hn : n3 5 (52 : Fin 88) = 35078003847440647647750000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![0,0],![0,2]] = ((42346556117392673697 : ℚ)/5000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![0,0],![1,1]] = ((416957358907607326303 : ℚ)/2500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![0,0],![2,0]] = ((42346556117392673697 : ℚ)/5000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![0,1],![0,1]] = ((316278450927 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![0,1],![1,0]] = ((316278450927 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![0,2],![0,0]] = ((211732743947251737111 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![1,0],![0,1]] = ((316278450927 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![1,0],![1,0]] = ((316278450927 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![1,1],![0,0]] = ((2084786407752748262889 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88)
      ![![2,0],![0,0]] = ((211732743947251737111 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (52 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (52 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1706941973599197420490753944400 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (49 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1903221507207457138967820555797 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (49 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1870916440767259495935946810312 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (50 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1702298671782622619921951347425 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (50 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119889819980768000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (51 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1101761158916581556090279376349 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (51 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1925687572790809583452955339229 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (52 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_5_49_1, L3C.mx_5_49_2, L3C.mx_5_50_1, L3C.mx_5_50_2, L3C.mx_5_51_1, L3C.mx_5_51_2, L3C.mx_5_52_1⟩
