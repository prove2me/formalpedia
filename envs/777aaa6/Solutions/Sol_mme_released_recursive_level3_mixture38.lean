-- Prove2me | solution 1 for mme_released_recursive_level3_mixture38
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T15:52:55.654443+00:00
-- url     : https://prove2.me/submissions/7b3eff07-2da5-4c09-b4cf-88bacc46e9f3

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

theorem mx_1_42_1 :
    (1891594772942995382893279158235 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 1 ⟨(42 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 1 ⟨(42 : Fin 88), complement (htotal3 1 (42 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (42 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (42 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (42 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (42 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (42 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (42 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 1 (42 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 1 (42 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 1 (42 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 72041155136932960881336148657154872520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 12196102489358956648810530056146685690254960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 72041155136932960881336148657154872520000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 1 ⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 12196246571669230514732292728444000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((590683 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((49999409317 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((590683 : ℚ)/100000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (42 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 6098850298430332514427543676292000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(42 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 737812451289000779029723747885156000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 737812451289000779029723747885156000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 1 ⟨(42 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 1475624902578001558059447495770312000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(42 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (42 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 737812063889246257682378923137592000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(42 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 160046617006357399010857114720818781488000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1375395996691659932241177320494862558362437024000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 160046617006357399010857114720818781488000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 1 ⟨(42 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1375396316784893944955975342209092000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(42 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((29091 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((124999970909 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((29091 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (42 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 687697794556680202788467303978420000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 5357506648225348657910639018801216000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 1 ⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 5357506648225348657910639018801216000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (42 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2678753333801844558467241027225256000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(42 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10340904678008518635043205850490936000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10340904678008518635043205850490936000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 1 ⟨(42 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 20681809356017037270086411700981872000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(42 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (42 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10340904678008518635043205850490936000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 213899983462896310184686854736993439931386880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 4929706681299556037541265309327229120137226240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 213899983462896310184686854736993439931386880000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 1 ⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 5357506648225348657910639018801216000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((499066071 : ℚ)/12500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((5750933929 : ℚ)/6250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((499066071 : ℚ)/12500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (42 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2678753314423504099443397991575960000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1375396316784893944955975342209092000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 1 1 ⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 1375396316784893944955975342209092000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 1 (42 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 687698522228213742167508038230672000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 737812451289000779029723747885156000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 737812451289000779029723747885156000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 1 1 ⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 1475624902578001558059447495770312000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 1 (42 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 737812838688755300377068572632720000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 12196246571669230514732292728444000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 1 1 ⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 12196246571669230514732292728444000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 1 (42 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6097396273238898000304749052152000000000000000000000000 := by decide +kernel
  have hn : n3 1 (42 : Fin 88) = 18561628792168432026484000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![0,0],![0,2]] = ((1440473103888514431393 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![0,0],![1,1]] = ((21271362223611485568607 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![0,0],![2,0]] = ((1440473103888514431393 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![0,1],![0,1]] = ((9947040573 : ℚ)/62500000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![0,1],![1,0]] = ((9947040573 : ℚ)/62500000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![0,2],![0,0]] = ((576189237433020918581 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![1,0],![0,1]] = ((9947040573 : ℚ)/62500000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![1,0],![1,0]] = ((9947040573 : ℚ)/62500000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![1,1],![0,0]] = ((8508546797966979081419 : ℚ)/50000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88)
      ![![2,0],![0,0]] = ((576189237433020918581 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 1) (42 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 1) (42 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_42_2 :
    (1891843425732232824942598191472 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 2 ⟨(42 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 2 ⟨(42 : Fin 88), complement (htotal3 1 (42 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (42 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (42 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (42 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (42 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (42 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (42 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 1 (42 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 1 (42 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 1 (42 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 72041155136932960881336148657154872520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 12196102489358956648810530056146685690254960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 72041155136932960881336148657154872520000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 2 ⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 12196246571669230514732292728444000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((590683 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((49999409317 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((590683 : ℚ)/100000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (42 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 6098850298430332514427543676292000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(42 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 1475624902578001558059447495770312000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 2 ⟨(42 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 1475624902578001558059447495770312000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(42 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (42 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 737812063889246257682378923137592000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(42 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 687698158392446972477987671104546000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 687698158392446972477987671104546000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 2 ⟨(42 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1375396316784893944955975342209092000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(42 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (42 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 687697794556680202788467303978420000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 215746335273329631732666277587212347978171840000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 4926013977678689394445306463626791304043656320000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 215746335273329631732666277587212347978171840000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 2 ⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 5357506648225348657910639018801216000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((8053982923 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((91946017077 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((8053982923 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (42 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2678753333801844558467241027225256000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(42 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10340904678008518635043205850490936000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10340904678008518635043205850490936000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 2 ⟨(42 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 20681809356017037270086411700981872000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(42 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (42 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10340904678008518635043205850490936000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 5357506648225348657910639018801216000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 2 ⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 5357506648225348657910639018801216000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (42 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2678753314423504099443397991575960000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 687698158392446972477987671104546000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 687698158392446972477987671104546000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 1 2 ⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 1375396316784893944955975342209092000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 1 (42 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 687698522228213742167508038230672000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1475624902578001558059447495770312000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 1 2 ⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 1475624902578001558059447495770312000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 1 (42 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 737812838688755300377068572632720000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 12196246571669230514732292728444000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 1 2 ⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 12196246571669230514732292728444000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 1 (42 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6097396273238898000304749052152000000000000000000000000 := by decide +kernel
  have hn : n3 1 (42 : Fin 88) = 18561628792168432026484000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![0,0],![0,2]] = ((581162377885070696759 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![0,0],![1,1]] = ((8638566094514929303241 : ℚ)/50000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![0,0],![2,0]] = ((581162377885070696759 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![0,1],![0,1]] = ((631210823467 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![0,1],![1,0]] = ((631210823467 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![0,2],![0,0]] = ((58116238213552093537 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![1,0],![0,1]] = ((631210823467 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![1,0],![1,0]] = ((631210823467 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![1,1],![0,0]] = ((863856797211447906463 : ℚ)/5000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88)
      ![![2,0],![0,0]] = ((58116238213552093537 : ℚ)/10000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 2) (42 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 2) (42 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_43_1 :
    (1386294361119888621995868000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (43 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 1 ⟨(43 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 1 ⟨(43 : Fin 88), complement (htotal3 1 (43 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (43 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (43 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (43 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (43 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (43 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (43 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(43 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 3360647362962696957191815729866000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3360647362962696957191815729866000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 1 ⟨(43 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 6721294725925393914383631459732000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(43 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (43 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3360646380250045313101579280472000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(43 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 165228389875217262118305587261400000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 1 ⟨(43 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 165228389875217262118305587261400000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(43 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (43 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 82614185957170232362764225972432000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(43 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 148955268061391434701655390639434000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 148955268061391434701655390639434000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 1 ⟨(43 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 297910536122782869403310781278868000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(43 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (43 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 148955270561752599284025074247108000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 297910536122782869403310781278868000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 1 ⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 297910536122782869403310781278868000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (43 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 148955265561030270119285707031760000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 82614194937608631059152793630700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 82614194937608631059152793630700000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 1 ⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 165228389875217262118305587261400000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (43 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 82614203918047029755541361288968000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 6721294725925393914383631459732000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 1 ⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 6721294725925393914383631459732000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (43 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 3360648345675348601282052179260000000000000000000000000 := by decide +kernel
  have hn : n3 1 (43 : Fin 88) = 469860220723925525436000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (43 : Fin 88)
      ![![0,0],![0,1]] = ((499999977657 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (43 : Fin 88)
      ![![0,0],![1,0]] = ((499999977657 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (43 : Fin 88)
      ![![0,1],![0,0]] = ((500000022343 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (43 : Fin 88)
      ![![1,0],![0,0]] = ((500000022343 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 1) (43 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 1) (43 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_43_2 :
    (1897610890791075391224338240998 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 2 ⟨(43 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 2 ⟨(43 : Fin 88), complement (htotal3 1 (43 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (43 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (43 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (43 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (43 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (43 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (43 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(43 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 6721294725925393914383631459732000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 2 ⟨(43 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 6721294725925393914383631459732000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(43 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (43 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3360646380250045313101579280472000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(43 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 5849415121792211337694691465239601548528200000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 153529559631632839442916204330920796902943600000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 5849415121792211337694691465239601548528200000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 2 ⟨(43 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 165228389875217262118305587261400000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(43 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((35401997963 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((464598002037 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((35401997963 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (43 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 82614185957170232362764225972432000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(43 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 148955268061391434701655390639434000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 148955268061391434701655390639434000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 2 ⟨(43 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 297910536122782869403310781278868000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(43 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (43 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 148955270561752599284025074247108000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 148955268061391434701655390639434000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 148955268061391434701655390639434000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 2 ⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 297910536122782869403310781278868000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (43 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 148955265561030270119285707031760000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 165228389875217262118305587261400000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 2 ⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 165228389875217262118305587261400000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (43 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 82614203918047029755541361288968000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 6721294725925393914383631459732000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 2 ⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 6721294725925393914383631459732000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (43 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 3360648345675348601282052179260000000000000000000000000 := by decide +kernel
  have hn : n3 1 (43 : Fin 88) = 469860220723925525436000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![0,0],![0,2]] = ((3112316971966041483397 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![0,0],![1,1]] = ((42632592083783958516603 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![0,0],![2,0]] = ((3112316971966041483397 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![0,1],![0,1]] = ((634040769963 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![0,1],![1,0]] = ((634040769963 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![0,2],![0,0]] = ((1556158147663827208289 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![1,0],![0,1]] = ((634040769963 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![1,0],![1,0]] = ((634040769963 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![1,1],![0,0]] = ((21316291079086172791711 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88)
      ![![2,0],![0,0]] = ((1556158147663827208289 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 2) (43 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 2) (43 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_44_1 :
    (1386294361119888602465248000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (44 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 1 ⟨(44 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 1 ⟨(44 : Fin 88), complement (htotal3 1 (44 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (44 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (44 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (44 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (44 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(44 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12875034209859797711609250010812000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12875034209859797711609250010812000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 1 ⟨(44 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 25750068419719595423218500021624000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(44 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (44 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12875036679305397178263663666504000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84537350608758561588781499978376000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 1 ⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 84537350608758561588781499978376000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (44 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42268675297651748233653582411456000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(44 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42268675304379280794390749989188000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42268675304379280794390749989188000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 1 ⟨(44 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 84537350608758561588781499978376000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(44 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (44 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42268675311106813355127917566920000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25750068419719595423218500021624000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 1 ⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 25750068419719595423218500021624000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (44 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12875031740414198244954836355120000000000000000000000000 := by decide +kernel
  have hn : n3 1 (44 : Fin 88) = 110287419028478157012000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (44 : Fin 88)
      ![![0,0],![0,1]] = ((124999994387 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (44 : Fin 88)
      ![![0,0],![1,0]] = ((124999994387 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (44 : Fin 88)
      ![![0,1],![0,0]] = ((125000005613 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (44 : Fin 88)
      ![![1,0],![0,0]] = ((125000005613 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 1) (44 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 1) (44 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_44_2 :
    (1386294361119888624318864000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (44 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 2 ⟨(44 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 2 ⟨(44 : Fin 88), complement (htotal3 1 (44 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (44 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (44 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (44 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (44 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(44 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12875034209859797711609250010812000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12875034209859797711609250010812000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 2 ⟨(44 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 25750068419719595423218500021624000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(44 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (44 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12875036679305397178263663666504000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42268675304379280794390749989188000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42268675304379280794390749989188000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 2 ⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 84537350608758561588781499978376000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (44 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42268675297651748233653582411456000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(44 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84537350608758561588781499978376000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 2 ⟨(44 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 84537350608758561588781499978376000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(44 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (44 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42268675311106813355127917566920000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25750068419719595423218500021624000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 2 ⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 25750068419719595423218500021624000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (44 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12875031740414198244954836355120000000000000000000000000 := by decide +kernel
  have hn : n3 1 (44 : Fin 88) = 110287419028478157012000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (44 : Fin 88)
      ![![0,0],![0,1]] = ((49999997767 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (44 : Fin 88)
      ![![0,0],![1,0]] = ((49999997767 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (44 : Fin 88)
      ![![0,1],![0,0]] = ((50000002233 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (44 : Fin 88)
      ![![1,0],![0,0]] = ((50000002233 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 2) (44 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 2) (44 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_45_1 :
    (1810466160508450113396294227317 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 1 ⟨(45 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 1 ⟨(45 : Fin 88), complement (htotal3 1 (45 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,2],![2,2]] + g ![![1,1],![2,2]] + g ![![1,2],![1,2]] + g ![![1,2],![2,1]] + g ![![2,0],![2,2]] + g ![![2,1],![1,2]] + g ![![2,1],![2,1]] + g ![![2,2],![0,2]] + g ![![2,2],![1,1]] + g ![![2,2],![2,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (45 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (45 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (45 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (45 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (45 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (45 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(45 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42177999473752421346594303219530000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42177999473752421346594303219530000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 1 ⟨(45 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84355998947504842693188606439060000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(45 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (45 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42201699844807346135577767996180000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(45 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25832258368801458726811393560940000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 1 ⟨(45 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25832258368801458726811393560940000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(45 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (45 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12923697809027521589201461965840000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(45 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 463555325662514378574852389995110243443960000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 24905147717476429969661688780949779513112080000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 463555325662514378574852389995110243443960000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 1 ⟨(45 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25832258368801458726811393560940000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(45 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((8972411917 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((241027588083 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((8972411917 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (45 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12908560559773937137609931595100000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(45 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42177999473752421346594303219530000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42177999473752421346594303219530000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 1 ⟨(45 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84355998947504842693188606439060000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(45 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (45 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42154299102697496557610838442880000000000000000000000000 := by decide +kernel
  have hn : n3 1 (45 : Fin 88) = 110188257316306301420000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![0,2],![2,2]] = ((210223712433088835677 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![1,1],![2,2]] = ((5647279107816911164323 : ℚ)/50000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![1,2],![1,2]] = ((765562510943 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![1,2],![2,1]] = ((765562510943 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![2,0],![2,2]] = ((210223712433088835677 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![2,1],![1,2]] = ((765562510943 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![2,1],![2,1]] = ((765562510943 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![2,2],![0,2]] = ((263087789610284928471 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![2,2],![1,1]] = ((7067376751139715071529 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88)
      ![![2,2],![2,0]] = ((263087789610284928471 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 1) (45 : Fin 88)) _ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 1) (45 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1891594772942995382893279158235 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (42 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1891843425732232824942598191472 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (42 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119888621995868000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (43 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1897610890791075391224338240998 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (43 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119888602465248000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (44 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119888624318864000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (44 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1810466160508450113396294227317 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (45 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_1_42_1, L3C.mx_1_42_2, L3C.mx_1_43_1, L3C.mx_1_43_2, L3C.mx_1_44_1, L3C.mx_1_44_2, L3C.mx_1_45_1⟩
