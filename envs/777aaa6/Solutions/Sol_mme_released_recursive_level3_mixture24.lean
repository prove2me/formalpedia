-- Prove2me | solution 1 for mme_released_recursive_level3_mixture24
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T13:30:22.903253+00:00
-- url     : https://prove2.me/submissions/4405aacc-cb95-41f0-9d00-d398280166a7

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

theorem mx_0_84_1 :
    (1870904959577055868796429701719 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(84 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(84 : Fin 88), complement (htotal3 0 (84 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (84 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (84 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (84 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (84 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (84 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (84 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (84 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (84 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 0 (84 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 0 (84 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 37122309794194286966441371964800000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 37122309794194286966441371964800000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 74244619588388573932882743929600000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 37122360148084480951506694098880000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 26992957098477381919567996713560024296549440000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 445410186394109684181841321802639951406901120000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 26992957098477381919567996713560024296549440000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 499396100591064448020977315229760000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((54051197169 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((445948802831 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((54051197169 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 249698334638928332901895261040480000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 548768205292322505074196421677760000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 548768205292322505074196421677760000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 274384148769962737503651756136000000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 7096315021623540139597372844015600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 7096315021623540139597372844015600000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 14192630043247080279194745688031200000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7096314761948121234902153901770240000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 141389799074269344374185585344306676590984000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7022976668525716611108826660443066646818032000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 141389799074269344374185585344306676590984000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 7305756266674255299857197831131680000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((387064101 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((9612935899 : ℚ)/10000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((387064101 : ℚ)/20000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3652878066096813812722576152743040000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 7305756266674255299857197831131680000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 7305756266674255299857197831131680000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3652878200577441487134621678388640000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 7096315021623540139597372844015600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 7096315021623540139597372844015600000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 14192630043247080279194745688031200000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 7096315281298959044292591786260960000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 27820523925635900546718495357164555111560640000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 493127157441050703980759430963430889776878720000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 27820523925635900546718495357164555111560640000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 548768205292322505074196421677760000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((50696311589 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((449303688411 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((50696311589 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (84 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 274384056522359767570544665541760000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 499396100591064448020977315229760000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 499396100591064448020977315229760000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 0 (84 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 249697765952136115119082054189280000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(84 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 37122309794194286966441371964800000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 37122309794194286966441371964800000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 0 1 ⟨(84 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 74244619588388573932882743929600000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(84 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 0 (84 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 37122259440304092981376049830720000000000000000000000000 := by decide +kernel
  have hn : n3 0 (84 : Fin 88) = 22620795235393111106080000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![0,0],![0,2]] = ((4336789546913013271379 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![0,0],![1,1]] = ((87988879640086986728621 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![0,0],![2,0]] = ((4336789546913013271379 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![0,1],![0,1]] = ((126139461627 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![0,1],![1,0]] = ((126139461627 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![0,2],![0,0]] = ((4336790583965747417847 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![1,0],![0,1]] = ((126139461627 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![1,0],![1,0]] = ((126139461627 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![1,1],![0,0]] = ((87988886161534252582153 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88)
      ![![2,0],![0,0]] = ((4336790583965747417847 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (84 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (84 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_84_2 :
    (1703864892709364422024028979834 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 2 ⟨(84 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 2 ⟨(84 : Fin 88), complement (htotal3 0 (84 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (84 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (84 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (84 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (84 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (84 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (84 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (84 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (84 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 0 (84 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 0 (84 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 37122309794194286966441371964800000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 37122309794194286966441371964800000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 74244619588388573932882743929600000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 37122360148084480951506694098880000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 26992957098477381919567996713560024296549440000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 445410186394109684181841321802639951406901120000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 26992957098477381919567996713560024296549440000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 499396100591064448020977315229760000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((54051197169 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((445948802831 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((54051197169 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 249698334638928332901895261040480000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 274384102646161252537098210838880000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 274384102646161252537098210838880000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 548768205292322505074196421677760000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 274384148769962737503651756136000000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 14192630043247080279194745688031200000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 14192630043247080279194745688031200000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7096314761948121234902153901770240000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 3652878133337127649928598915565840000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3652878133337127649928598915565840000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 7305756266674255299857197831131680000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3652878066096813812722576152743040000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 416471760752532603302332876199130679454891360000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6472812745169190093252532078733418641090217280000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 416471760752532603302332876199130679454891360000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 7305756266674255299857197831131680000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((57005975227 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((442994024773 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((57005975227 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3652878200577441487134621678388640000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 7096315021623540139597372844015600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 7096315021623540139597372844015600000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 14192630043247080279194745688031200000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 7096315281298959044292591786260960000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 548768205292322505074196421677760000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 548768205292322505074196421677760000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (84 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 274384056522359767570544665541760000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 249698050295532224010488657614880000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 249698050295532224010488657614880000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 499396100591064448020977315229760000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 0 (84 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 249697765952136115119082054189280000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(84 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 74244619588388573932882743929600000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 0 2 ⟨(84 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 74244619588388573932882743929600000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(84 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 0 (84 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 37122259440304092981376049830720000000000000000000000000 := by decide +kernel
  have hn : n3 0 (84 : Fin 88) = 22620795235393111106080000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![0,0],![1,2]] = ((6885397103 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![0,0],![2,1]] = ((6885397103 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![0,1],![0,2]] = ((1960429219361624520471 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![0,1],![1,1]] = ((46662490527238375479529 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![0,1],![2,0]] = ((1960429219361624520471 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![0,2],![0,1]] = ((980214779455574215553 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![0,2],![1,0]] = ((980214779455574215553 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![1,0],![0,2]] = ((1960429219361624520471 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![1,0],![1,1]] = ((46662490527238375479529 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![1,0],![2,0]] = ((1960429219361624520471 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq10 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![1,1],![0,1]] = ((23331245500144425784447 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq11 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![1,1],![1,0]] = ((23331245500144425784447 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq12 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![1,2],![0,0]] = ((860675171 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq13 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![2,0],![0,1]] = ((980214779455574215553 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq14 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![2,0],![1,0]] = ((980214779455574215553 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq15 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88)
      ![![2,1],![0,0]] = ((860675171 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 2) (84 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 2) (84 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_85_1 :
    (1718924780906465795321853912645 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(85 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(85 : Fin 88), complement (htotal3 0 (85 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (85 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (85 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (85 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (85 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (85 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (85 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (85 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (85 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 0 (85 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 0 (85 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 18185193804362277578005894975862313149725696000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 620360844989833948968386527209299373700548608000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18185193804362277578005894975862313149725696000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 656731232598558504124398317161024000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((1730654119 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((29519345881 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1730654119 : ℚ)/62500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (85 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 328366499102913884839434360044672000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 46051572062227627199581578563808000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 46051572062227627199581578563808000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 92103144124455254399163157127616000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (85 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46051833337825784939892097367744000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 5002160835796336648178233872623632000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 5002160835796336648178233872623632000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 10004321671592673296356467745247264000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5002160884504327097755802595907744000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 148080729704245822252019012731157762122734432000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 18849510464870230600663335687805556475754531136000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 148080729704245822252019012731157762122734432000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 19145671924278722245167373713267872000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((7734423231 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((492265576769 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((7734423231 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9572834248423010994483673111153440000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 353127782341679648840298533598112000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 353127782341679648840298533598112000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 706255564683359297680597067196224000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (85 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 353128767611133964423503000255616000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 706255564683359297680597067196224000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 706255564683359297680597067196224000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 353126797072225333257094066940608000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 9572835962139361122583686856633936000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9572835962139361122583686856633936000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 19145671924278722245167373713267872000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9572837675855711250683700602114432000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 515260140428404380912243950761712840871851104000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8973801390735864534531979843723838318256297792000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 515260140428404380912243950761712840871851104000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 10004321671592673296356467745247264000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((51503755811 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((448496244189 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((51503755811 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (85 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5002160787088346198600665149339520000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 92103144124455254399163157127616000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 92103144124455254399163157127616000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 0 (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46051310786629469459271059759872000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 328365616299279252062199158580512000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 328365616299279252062199158580512000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 0 1 ⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 656731232598558504124398317161024000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 0 (85 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 328364733495644619284963957116352000000000000000000000000 := by decide +kernel
  have hn : n3 0 (85 : Fin 88) = 30605083537277768597728000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![0,0],![1,2]] = ((1304286941 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![0,0],![2,1]] = ((1304286941 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![0,1],![0,2]] = ((11134196803333546847653 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![0,1],![1,1]] = ((232344362497166453152347 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![0,1],![2,0]] = ((11134196803333546847653 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![0,2],![0,1]] = ((11134197370689746886541 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![0,2],![1,0]] = ((11134197370689746886541 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![1,0],![0,2]] = ((11134196803333546847653 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![1,0],![1,1]] = ((232344362497166453152347 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![1,0],![2,0]] = ((11134196803333546847653 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq10 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![1,1],![0,1]] = ((232344333188810253113459 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq11 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![1,1],![1,0]] = ((232344333188810253113459 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq12 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![1,2],![0,0]] = ((1304295087 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq13 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![2,0],![0,1]] = ((11134197370689746886541 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq14 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![2,0],![1,0]] = ((11134197370689746886541 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq15 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88)
      ![![2,1],![0,0]] = ((1304295087 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (85 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (85 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_85_2 :
    (1864183010100502142907807335345 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 2 ⟨(85 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 2 ⟨(85 : Fin 88), complement (htotal3 0 (85 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (85 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (85 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (85 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (85 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (85 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (85 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (85 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (85 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 0 (85 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 0 (85 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 18185193804362277578005894975862313149725696000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 620360844989833948968386527209299373700548608000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18185193804362277578005894975862313149725696000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 656731232598558504124398317161024000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((1730654119 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((29519345881 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1730654119 : ℚ)/62500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (85 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 328366499102913884839434360044672000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 46051572062227627199581578563808000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 46051572062227627199581578563808000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 92103144124455254399163157127616000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (85 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46051833337825784939892097367744000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 181825189711180941044349061155098202347488192000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9640671292170311414267769622937067595305023616000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 181825189711180941044349061155098202347488192000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 10004321671592673296356467745247264000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((9087332239 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((240912667761 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((9087332239 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5002160884504327097755802595907744000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 9572835962139361122583686856633936000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9572835962139361122583686856633936000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 19145671924278722245167373713267872000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9572834248423010994483673111153440000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 706255564683359297680597067196224000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 706255564683359297680597067196224000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (85 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 353128767611133964423503000255616000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39095344048929418726664066305572545661509248000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 628064876585500460227268934585078908676981504000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39095344048929418726664066305572545661509248000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 706255564683359297680597067196224000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((27677901601 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((222322098399 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((27677901601 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 353126797072225333257094066940608000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 9572835962139361122583686856633936000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9572835962139361122583686856633936000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 19145671924278722245167373713267872000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9572837675855711250683700602114432000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 10004321671592673296356467745247264000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 10004321671592673296356467745247264000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (85 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5002160787088346198600665149339520000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 46051572062227627199581578563808000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 46051572062227627199581578563808000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 92103144124455254399163157127616000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 0 (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46051310786629469459271059759872000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 656731232598558504124398317161024000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 0 2 ⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 656731232598558504124398317161024000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 0 (85 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 328364733495644619284963957116352000000000000000000000000 := by decide +kernel
  have hn : n3 0 (85 : Fin 88) = 30605083537277768597728000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![0,0],![0,2]] = ((9765770843796631521 : ℚ)/2500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![0,0],![1,1]] = ((222371084838703368479 : ℚ)/1250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![0,0],![2,0]] = ((9765770843796631521 : ℚ)/2500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![0,1],![0,1]] = ((628581034421 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![0,1],![1,0]] = ((628581034421 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![0,2],![0,0]] = ((1953153214346421339831 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![1,0],![0,1]] = ((628581034421 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![1,0],![1,0]] = ((628581034421 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![1,1],![0,0]] = ((44474217043903578660169 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88)
      ![![2,0],![0,0]] = ((1953153214346421339831 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 2) (85 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 2) (85 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_86_1 :
    (1123569799486962625221762437318 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(86 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(86 : Fin 88), complement (htotal3 0 (86 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (86 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (86 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (86 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (86 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (86 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (86 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (86 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (86 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 403102398480902086641476652373446000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 403102398480902086641476652373446000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 806204796961804173282953304746892000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (86 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 403102256086526220601595356016109000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 21344626718667803911298727202491000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 21344626718667803911298727202491000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (86 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10672472700715639630395089053158000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 33886269489700002496737213571522760096436474000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 27917612990265460324830867134437488479807127052000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 33886269489700002496737213571522760096436474000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 27985385529244860329824341561580534000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((1210855911 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((498789144089 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1210855911 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13992692909717786558598425027945962000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2062925984795705497700203203235041500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2062925984795705497700203203235041500000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4125851969591410995400406406470083000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (86 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2062925966465270575319635555438868000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(86 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 2062925984795705497700203203235041500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2062925984795705497700203203235041500000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 1 ⟨(86 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 4125851969591410995400406406470083000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(86 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2062926003126140420080770851031215000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1317696133549983994071158640793586762311288584000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25349993262144892341682024279993360475377422832000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1317696133549983994071158640793586762311288584000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 1 ⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 27985385529244860329824341561580534000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((11771288019 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((113228711981 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((11771288019 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (86 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 13992692619527073771225916533634572000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 21344626718667803911298727202491000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 1 ⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 21344626718667803911298727202491000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (86 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10672154017952164280903638149333000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(86 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 403102398480902086641476652373446000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 403102398480902086641476652373446000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 1 ⟨(86 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 806204796961804173282953304746892000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(86 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (86 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 403102540875277952681357948730783000000000000000000000000 := by decide +kernel
  have hn : n3 0 (86 : Fin 88) = 32938786922516743302419000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![0,0],![2,2]] = ((323999607 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![0,1],![1,2]] = ((37433505821 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![0,1],![2,1]] = ((37433505821 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![0,2],![0,2]] = ((6054944266633505433826894127037 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![0,2],![1,1]] = ((1276231187834606924745298105872963 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![0,2],![2,0]] = ((6054944266633505433826894127037 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![1,0],![1,2]] = ((37433505821 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![1,0],![2,1]] = ((37433505821 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![1,1],![0,2]] = ((1276231213094141250598423105872963 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![1,1],![1,1]] = ((23992044454367118319222451894127037 : ℚ)/31250000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![1,1],![2,0]] = ((1276231213094141250598423105872963 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![1,2],![0,1]] = ((74867001883 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![1,2],![1,0]] = ((74867001883 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![2,0],![0,2]] = ((6054944266633505433826894127037 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![2,0],![1,1]] = ((1276231187834606924745298105872963 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![2,0],![2,0]] = ((6054944266633505433826894127037 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq16 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![2,1],![0,1]] = ((74867001883 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq17 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![2,1],![1,0]] = ((74867001883 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq18 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88)
      ![![2,2],![0,0]] = ((162004641 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (86 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (86 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_86_2 :
    (1386294361119890548308060000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (86 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 2 ⟨(86 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 2 ⟨(86 : Fin 88), complement (htotal3 0 (86 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (86 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (86 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (86 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (86 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (86 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (86 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (86 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (86 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 403102398480902086641476652373446000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 403102398480902086641476652373446000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 2 ⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 806204796961804173282953304746892000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (86 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 403102256086526220601595356016109000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 21344626718667803911298727202491000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 2 ⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 21344626718667803911298727202491000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (86 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10672472700715639630395089053158000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 13992692764622430164912170780790267000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 13992692764622430164912170780790267000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 2 ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 27985385529244860329824341561580534000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13992692909717786558598425027945962000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4125851969591410995400406406470083000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 2 ⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4125851969591410995400406406470083000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (86 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2062925966465270575319635555438868000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(86 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 2062925984795705497700203203235041500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2062925984795705497700203203235041500000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 2 ⟨(86 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 4125851969591410995400406406470083000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(86 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2062926003126140420080770851031215000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 27985385529244860329824341561580534000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 2 ⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 27985385529244860329824341561580534000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (86 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 13992692619527073771225916533634572000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10672313359333901955649363601245500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10672313359333901955649363601245500000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 2 ⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 21344626718667803911298727202491000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (86 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10672154017952164280903638149333000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(86 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 806204796961804173282953304746892000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 2 ⟨(86 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 806204796961804173282953304746892000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(86 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (86 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 403102540875277952681357948730783000000000000000000000000 := by decide +kernel
  have hn : n3 0 (86 : Fin 88) = 32938786922516743302419000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (86 : Fin 88)
      ![![0,0],![0,1]] = ((500000004199 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (86 : Fin 88)
      ![![0,0],![1,0]] = ((500000004199 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (86 : Fin 88)
      ![![0,1],![0,0]] = ((499999995801 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (86 : Fin 88)
      ![![1,0],![0,0]] = ((499999995801 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 2) (86 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 2) (86 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_87_1 :
    (1386293786274521517324960378023 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (87 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(87 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(87 : Fin 88), complement (htotal3 0 (87 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (87 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (87 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (87 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (87 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(87 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12522125442961834518084987125608000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12522125442961834518084987125608000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(87 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 25044250885923669036169974251216000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(87 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (87 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12526845331011209270134608701176000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(87 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84581398588867641271830025748784000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(87 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 84581398588867641271830025748784000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(87 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (87 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42236732463111494686479286464888000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(87 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42290699294433820635915012874392000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42290699294433820635915012874392000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(87 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 84581398588867641271830025748784000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(87 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (87 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42344666125756146585350739283896000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(87 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25044250885923669036169974251216000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(87 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 25044250885923669036169974251216000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(87 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (87 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12517405554912459766035365550040000000000000000000000000 := by decide +kernel
  have hn : n3 0 (87 : Fin 88) = 109625649474791310308000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (87 : Fin 88)
      ![![0,0],![0,1]] = ((124866165629 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (87 : Fin 88)
      ![![0,0],![1,0]] = ((124866165629 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (87 : Fin 88)
      ![![0,1],![0,0]] = ((125133834371 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (87 : Fin 88)
      ![![1,0],![0,0]] = ((125133834371 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (87 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (87 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1870904959577055868796429701719 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (84 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 4 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1703864892709364422024028979834 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (84 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1718924780906465795321853912645 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (85 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1864183010100502142907807335345 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (85 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1123569799486962625221762437318 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (86 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119890548308060000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (86 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386293786274521517324960378023 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (87 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_0_84_1, L3C.mx_0_84_2, L3C.mx_0_85_1, L3C.mx_0_85_2, L3C.mx_0_86_1, L3C.mx_0_86_2, L3C.mx_0_87_1⟩
