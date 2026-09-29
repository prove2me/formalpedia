-- Prove2me | solution 1 for mme_released_recursive_level3_mixture145
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T21:30:43.4811+00:00
-- url     : https://prove2.me/submissions/8807db88-f8a9-472b-a221-f6af8a0d9135

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

theorem mx_5_52_2 :
    (1044542431116368809623087302558 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(52 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(52 : Fin 88), complement (htotal3 5 (52 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 22427966403115820596943672672250000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 22427966403115820596943672672250000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11215249955971850998860015708000000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1273318214037064922699173010667375000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1273318214037064922699173010667375000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2546636428074129845398346021334750000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1273317551185565219536974734959500000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 539206272592066582799127196394358228211452000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9215474222020517792178795426172283543577096000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 539206272592066582799127196394358228211452000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 10293886767204650957777049818961000000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((13095303183 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((111904696817 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((13095303183 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5146943387671373925191640036619500000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1286427838436566363084006897219125000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1286427838436566363084006897219125000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2572855676873132726168013794438250000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1286427169867352032788983054928000000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(52 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 61015560599243702315751016359104304247125000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 39162362896572749190987791352469291391505750000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 61015560599243702315751016359104304247125000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(52 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 39284394017771236595619293385187500000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(52 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((776587779 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((249223412221 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((776587779 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19642197008885618297809646692593750000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(52 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1286427838436566363084006897219125000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1286427838436566363084006897219125000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(52 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 2572855676873132726168013794438250000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(52 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1286428507005780693379030739510250000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 538805238379442515447267705481196083015289000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9216276290445765926882514407998607833969422000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 538805238379442515447267705481196083015289000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 2 ⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10293886767204650957777049818961000000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((52342254249 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((447657745751 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((52342254249 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5146943379533277032585409782341500000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(52 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1273318214037064922699173010667375000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1273318214037064922699173010667375000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 2 ⟨(52 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 2546636428074129845398346021334750000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(52 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1273318876888564625861371286375250000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(52 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 22427966403115820596943672672250000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 5 2 ⟨(52 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 22427966403115820596943672672250000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(52 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 5 (52 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11212716447143969598083656964250000000000000000000000000 := by decide +kernel
  have hn : n3 5 (52 : Fin 88) = 35078003847440647647750000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![0,0],![2,2]] = ((319650927 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![0,1],![1,2]] = ((36486502981 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![0,1],![2,1]] = ((36486502981 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![0,2],![0,2]] = ((201484211261799267642806160079653 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![0,2],![1,1]] = ((1827969696172729768742193839920347 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![0,2],![2,0]] = ((201484211261799267642806160079653 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![1,0],![1,2]] = ((36486502981 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![1,0],![2,1]] = ((36486502981 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![1,1],![0,2]] = ((1827969696171599972735193839920347 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![1,1],![1,1]] = ((49480994515706370990879806160079653 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![1,1],![2,0]] = ((1827969696171599972735193839920347 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![1,2],![0,1]] = ((1459458601 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![1,2],![1,0]] = ((1459458601 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![2,0],![0,2]] = ((201484211261799267642806160079653 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![2,0],![1,1]] = ((1827969696172729768742193839920347 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![2,0],![2,0]] = ((201484211261799267642806160079653 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq16 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![2,1],![0,1]] = ((1459458601 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq17 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![2,1],![1,0]] = ((1459458601 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq18 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88)
      ![![2,2],![0,0]] = ((19982697 : ℚ)/62500000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (52 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (52 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_53_1 :
    (1847021862612527177288714587233 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(53 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(53 : Fin 88), complement (htotal3 5 (53 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (53 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (53 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (53 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (53 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (53 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (53 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 5 (53 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 5 (53 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4692038947879554628174331018208000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 4692038947879554628174331018208000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2346024570963464258601308529960000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 438679652210352763054460434613520000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 438679652210352763054460434613520000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 877359304420705526108920869227040000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 438679728622815862282948056983688000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 280423065509481684473185647511556292136406400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5530726192782489187658631231555127415727187200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 280423065509481684473185647511556292136406400000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 6091572323801452556605002526578240000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((4603459511 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((45396540489 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((4603459511 : ℚ)/100000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3045786105004216426421171579834712000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 87538578017024759884951136588256000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 87538578017024759884951136588256000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 175077156034049519769902273176512000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (53 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87538673866805397405351739145952000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 175077156034049519769902273176512000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 175077156034049519769902273176512000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87538482167244122364550534030560000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(53 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 3045786161900726278302501263289120000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3045786161900726278302501263289120000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(53 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 6091572323801452556605002526578240000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(53 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3045786218797236130183830946743528000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(53 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 18491740119609279786884922869245377241507680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 840375824181486966535151023488549245516984640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18491740119609279786884922869245377241507680000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 1 ⟨(53 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 877359304420705526108920869227040000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(53 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((21076587467 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((478923412533 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((21076587467 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 438679575797889663825972812243352000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(53 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2346019473939777314087165509104000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2346019473939777314087165509104000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 1 ⟨(53 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4692038947879554628174331018208000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(53 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (53 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2346014376916090369573022488248000000000000000000000000 := by decide +kernel
  have hn : n3 5 (53 : Fin 88) = 7148700823204087157112000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![0,0],![1,2]] = ((2514708867 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![0,0],![2,1]] = ((2514708867 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![0,1],![0,2]] = ((20906932705749966444423 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![0,1],![1,1]] = ((222806298103250033555577 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![0,1],![2,0]] = ((20906932705749966444423 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![0,2],![0,1]] = ((20906931522395994613917 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![0,2],![1,0]] = ((20906931522395994613917 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![1,0],![0,2]] = ((20906932705749966444423 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![1,0],![1,1]] = ((222806298103250033555577 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![1,0],![2,0]] = ((20906932705749966444423 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![1,1],![0,1]] = ((222806280638604005386083 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![1,1],![1,0]] = ((222806280638604005386083 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![1,2],![0,0]] = ((502942789 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![2,0],![0,1]] = ((20906931522395994613917 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![2,0],![1,0]] = ((20906931522395994613917 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88)
      ![![2,1],![0,0]] = ((502942789 : ℚ)/80000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (53 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (53 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_53_2 :
    (1102342488576346345353732938494 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(53 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(53 : Fin 88), complement (htotal3 5 (53 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (53 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (53 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (53 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (53 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (53 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (53 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 5 (53 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 5 (53 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 4692038947879554628174331018208000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 4692038947879554628174331018208000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2346024570963464258601308529960000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 438679652210352763054460434613520000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 438679652210352763054460434613520000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 877359304420705526108920869227040000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 438679728622815862282948056983688000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 280423065509481684473185647511556292136406400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5530726192782489187658631231555127415727187200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 280423065509481684473185647511556292136406400000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 6091572323801452556605002526578240000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((4603459511 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((45396540489 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((4603459511 : ℚ)/100000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3045786105004216426421171579834712000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 87538578017024759884951136588256000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 87538578017024759884951136588256000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 175077156034049519769902273176512000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (53 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87538673866805397405351739145952000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 87538578017024759884951136588256000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 87538578017024759884951136588256000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 175077156034049519769902273176512000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87538482167244122364550534030560000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(53 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1661153041115760422719572628615116819912000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6088250017719221035759563381321009766360176000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1661153041115760422719572628615116819912000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(53 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 6091572323801452556605002526578240000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(53 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((10907877 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((19989092123 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10907877 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3045786218797236130183830946743528000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(53 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 438679652210352763054460434613520000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 438679652210352763054460434613520000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 5 2 ⟨(53 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 877359304420705526108920869227040000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(53 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 5 (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 438679575797889663825972812243352000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(53 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4692038947879554628174331018208000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 5 2 ⟨(53 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4692038947879554628174331018208000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(53 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 5 (53 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2346014376916090369573022488248000000000000000000000000 := by decide +kernel
  have hn : n3 5 (53 : Fin 88) = 7148700823204087157112000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![0,0],![2,2]] = ((328173529 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![0,1],![1,2]] = ((73610333217 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![0,1],![2,1]] = ((73610333217 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![0,2],![0,2]] = ((1069711959623381052101074161 : ℚ)/100000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![0,2],![1,1]] = ((985417974123108648932148925839 : ℚ)/50000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![0,2],![2,0]] = ((1069711959623381052101074161 : ℚ)/100000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![1,0],![1,2]] = ((73610333217 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![1,0],![2,1]] = ((73610333217 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![1,1],![0,2]] = ((985418010545003414373648925839 : ℚ)/50000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![1,1],![1,1]] = ((19331169066372264555642101074161 : ℚ)/25000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![1,1],![2,0]] = ((985418010545003414373648925839 : ℚ)/50000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![1,2],![0,1]] = ((73610327779 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![1,2],![1,0]] = ((73610327779 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![2,0],![0,2]] = ((1069711959623381052101074161 : ℚ)/100000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![2,0],![1,1]] = ((985417974123108648932148925839 : ℚ)/50000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![2,0],![2,0]] = ((1069711959623381052101074161 : ℚ)/100000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq16 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![2,1],![0,1]] = ((73610327779 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq17 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![2,1],![1,0]] = ((73610327779 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq18 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88)
      ![![2,2],![0,0]] = ((65634991 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (53 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (53 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_54_1 :
    (1386294361119889308828828000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (54 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(54 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(54 : Fin 88), complement (htotal3 5 (54 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (54 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (54 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (54 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (54 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (54 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (54 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 45755483389312062770756600692112000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 45755483389312062770756600692112000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (54 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22877638771957197394938911204588000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 597071775424651791853335174992846000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 597071775424651791853335174992846000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1194143550849303583706670349985692000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (54 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 597071833020306221590509684321196000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 2221898377015309192550573049322196000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2221898377015309192550573049322196000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (54 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1110949286377860108540622611241200000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(54 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1110949188507654596275286524661098000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1110949188507654596275286524661098000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(54 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2221898377015309192550573049322196000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(54 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1110949090637449084009950438080996000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1194143550849303583706670349985692000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1194143550849303583706670349985692000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 597071717828997362116160665664496000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(54 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 22877741694656031385378300346056000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 22877741694656031385378300346056000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(54 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 45755483389312062770756600692112000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(54 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22877844617354865375817689487524000000000000000000000000 := by decide +kernel
  have hn : n3 5 (54 : Fin 88) = 3461797411253924839028000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (54 : Fin 88)
      ![![0,0],![0,1]] = ((499999981903 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (54 : Fin 88)
      ![![0,0],![1,0]] = ((499999981903 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (54 : Fin 88)
      ![![0,1],![0,0]] = ((500000018097 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (54 : Fin 88)
      ![![1,0],![0,0]] = ((500000018097 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (54 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (54 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_54_2 :
    (1623451357420832305202095854175 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(54 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(54 : Fin 88), complement (htotal3 5 (54 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (54 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (54 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (54 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (54 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (54 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (54 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 45755483389312062770756600692112000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 45755483389312062770756600692112000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (54 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22877638771957197394938911204588000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 597071775424651791853335174992846000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 597071775424651791853335174992846000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1194143550849303583706670349985692000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (54 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 597071833020306221590509684321196000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1110949188507654596275286524661098000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1110949188507654596275286524661098000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2221898377015309192550573049322196000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (54 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1110949286377860108540622611241200000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(54 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 2221898377015309192550573049322196000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(54 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2221898377015309192550573049322196000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(54 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1110949090637449084009950438080996000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 56863238309685247524854390475860611786826100000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1080417074229933088656961569033970776426347800000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 56863238309685247524854390475860611786826100000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1194143550849303583706670349985692000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((1904737107 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((18095262893 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1904737107 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 597071717828997362116160665664496000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(54 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 22877741694656031385378300346056000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 22877741694656031385378300346056000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(54 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 45755483389312062770756600692112000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(54 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22877844617354865375817689487524000000000000000000000000 := by decide +kernel
  have hn : n3 5 (54 : Fin 88) = 3461797411253924839028000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![0,1],![2,2]] = ((6608660733 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![0,2],![1,2]] = ((82129636817567784081 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![0,2],![2,1]] = ((82129636817567784081 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![1,0],![2,2]] = ((6608660733 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![1,1],![1,2]] = ((2384826983627432215919 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![1,1],![2,1]] = ((2384826983627432215919 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![1,2],![0,2]] = ((328518610650398371749 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![1,2],![1,1]] = ((9539309667489601628251 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![1,2],![2,0]] = ((328518610650398371749 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![2,0],![1,2]] = ((82129636817567784081 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![2,0],![2,1]] = ((82129636817567784081 : ℚ)/20000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![2,1],![0,2]] = ((328518610650398371749 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![2,1],![1,1]] = ((9539309667489601628251 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![2,1],![2,0]] = ((328518610650398371749 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![2,2],![0,1]] = ((6608601271 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88)
      ![![2,2],![1,0]] = ((6608601271 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (54 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (54 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_55_1 :
    (1924730358798293928061377227471 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 1 ⟨(55 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 1 ⟨(55 : Fin 88), complement (htotal3 5 (55 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (55 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (55 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (55 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (55 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (55 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (55 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 50962100981824188209951855899785000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 1 ⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 50962100981824188209951855899785000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (55 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25480754834492379762926647116201000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1239974725106195486473314299770710000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1239974725106195486473314299770710000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 1 ⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2479949450212390972946628599541420000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1239975064905767915637513054547836000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 63637098125830314976703826937263066964818075000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1210118394412963929693011890684268866070363850000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 63637098125830314976703826937263066964818075000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 1 ⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 1337392590664624559646419544558795000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((9516591997 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((90483408003 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((9516591997 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 668696167784653962382617078102480000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1337392590664624559646419544558795000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 1 ⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1337392590664624559646419544558795000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 668696422879970597263802466456315000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(55 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1239974725106195486473314299770710000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1239974725106195486473314299770710000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 1 ⟨(55 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2479949450212390972946628599541420000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(55 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1239974385306623057309115544993584000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 1 ⟨(55 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1074097642664282058135750039909667003526040000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 48813905696495624093680355819965665992947920000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1074097642664282058135750039909667003526040000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 1 ⟨(55 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 50962100981824188209951855899785000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 1) ⟨(55 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2634550043 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((59865449957 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2634550043 : ℚ)/125000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25481346147331808447025208783584000000000000000000000000 := by decide +kernel
  have hn : n3 5 (55 : Fin 88) = 3868304141858839720803000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![0,0],![0,2]] = ((8364284848197455676673 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![0,0],![1,1]] = ((81362007637802544323327 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![0,0],![2,0]] = ((8364284848197455676673 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![0,1],![0,1]] = ((32054737157 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![0,1],![1,0]] = ((32054737157 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![0,2],![0,0]] = ((522767808256174528127 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![1,0],![0,1]] = ((32054737157 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![1,0],![1,0]] = ((32054737157 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![1,1],![0,0]] = ((5085128188243825471873 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88)
      ![![2,0],![0,0]] = ((522767808256174528127 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 1) (55 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 1) (55 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_5_55_2 :
    (1623470184003987223449031640700 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 5 2 ⟨(55 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 5 2 ⟨(55 : Fin 88), complement (htotal3 5 (55 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 5 (55 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 5 (55 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 5 (55 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 5 (55 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 5 (55 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 5 (55 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 50962100981824188209951855899785000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 5 2 ⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 50962100981824188209951855899785000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 5 (55 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25480754834492379762926647116201000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1239974725106195486473314299770710000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1239974725106195486473314299770710000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 5 2 ⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2479949450212390972946628599541420000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 5 (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1239975064905767915637513054547836000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 63637098125830314976703826937263066964818075000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1210118394412963929693011890684268866070363850000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 63637098125830314976703826937263066964818075000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 5 2 ⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 1337392590664624559646419544558795000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((9516591997 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((90483408003 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((9516591997 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 5 (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 668696167784653962382617078102480000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 668696295332312279823209772279397500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 668696295332312279823209772279397500000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 5 2 ⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1337392590664624559646419544558795000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 5 (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 668696422879970597263802466456315000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(55 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 2479949450212390972946628599541420000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 5 2 ⟨(55 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2479949450212390972946628599541420000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(55 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 5 (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1239974385306623057309115544993584000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 5 2 ⟨(55 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 25481050490912094104975927949892500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 25481050490912094104975927949892500000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 5 2 ⟨(55 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 50962100981824188209951855899785000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 5 2) ⟨(55 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 5 (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25481346147331808447025208783584000000000000000000000000 := by decide +kernel
  have hn : n3 5 (55 : Fin 88) = 3868304141858839720803000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![0,1],![2,2]] = ((205850429 : ℚ)/62500000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![0,2],![1,2]] = ((20563625446039929319 : ℚ)/5000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![0,2],![2,1]] = ((20563625446039929319 : ℚ)/5000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![1,0],![2,2]] = ((205850429 : ℚ)/62500000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![1,1],![1,2]] = ((596202301913960070681 : ℚ)/2500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![1,1],![2,1]] = ((596202301913960070681 : ℚ)/2500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![1,2],![0,2]] = ((329018132650970717537 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![1,2],![1,1]] = ((9539241537689029282463 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![1,2],![2,0]] = ((329018132650970717537 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![2,0],![1,2]] = ((20563625446039929319 : ℚ)/5000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![2,0],![2,1]] = ((20563625446039929319 : ℚ)/5000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![2,1],![0,2]] = ((329018132650970717537 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![2,1],![1,1]] = ((9539241537689029282463 : ℚ)/40000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![2,1],![2,0]] = ((329018132650970717537 : ℚ)/80000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![2,2],![0,1]] = ((6587060867 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88)
      ![![2,2],![1,0]] = ((6587060867 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 5) (n3 5) (m3 5)
      (mu3 5 2) (55 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 5) (n3 5) (m3 5)
        (mu3 5 2) (55 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1044542431116368809623087302558 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (52 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1847021862612527177288714587233 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (53 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1102342488576346345353732938494 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (53 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119889308828828000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (54 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1623451357420832305202095854175 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (54 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1924730358798293928061377227471 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 1) (55 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1623470184003987223449031640700 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 5) (n3 5) (m3 5) (mu3 5 2) (55 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_5_52_2, L3C.mx_5_53_1, L3C.mx_5_53_2, L3C.mx_5_54_1, L3C.mx_5_54_2, L3C.mx_5_55_1, L3C.mx_5_55_2⟩
