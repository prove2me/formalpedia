-- Prove2me | solution 1 for mme_released_recursive_level3_mixture10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T11:31:44.521505+00:00
-- url     : https://prove2.me/submissions/68ac5162-e7fd-4acd-9fbe-86d0413208e9

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

theorem mx_0_35_1 :
    (1818103397108687862766343975068 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 0 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 0 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(35 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(35 : Fin 88), complement (htotal3 0 (35 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,2],![2,2]] + g ![![1,1],![2,2]] + g ![![1,2],![1,2]] + g ![![1,2],![2,1]] + g ![![2,0],![2,2]] + g ![![2,1],![1,2]] + g ![![2,1],![2,1]] + g ![![2,2],![0,2]] + g ![![2,2],![1,1]] + g ![![2,2],![2,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (35 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (35 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (35 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (35 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42278959891440783148357026710847500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42278959891440783148357026710847500000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84557919782881566296714053421695000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (35 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42278882093222561070450088417950000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 26297888449387912018285946578305000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 26297888449387912018285946578305000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (35 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13149778221817225416934536135210000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(35 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 554254735213610642746948394819655907452825000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25189378978960690732792049788665688185094350000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 554254735213610642746948394819655907452825000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(35 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 26297888449387912018285946578305000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(35 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((4215203333 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((95784796667 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((4215203333 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13148110227570686601351410443095000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42278959891440783148357026710847500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42278959891440783148357026710847500000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84557919782881566296714053421695000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (35 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42279037689659005226263965003745000000000000000000000000 := by decide +kernel
  have hn : n3 0 (35 : Fin 88) = 110855808232269478315000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![0,2],![2,2]] = ((499946362194979138329 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![1,1],![2,2]] = ((11360605139105020861671 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![1,2],![1,2]] = ((762773923453 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![1,2],![2,1]] = ((762773923453 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![2,0],![2,2]] = ((499946362194979138329 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![2,1],![1,2]] = ((762773923453 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![2,1],![2,1]] = ((762773923453 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![2,2],![0,2]] = ((250004893170224196411 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![2,2],![1,1]] = ((5681023183529775803589 : ℚ)/50000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88)
      ![![2,2],![2,0]] = ((250004893170224196411 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (35 : Fin 88)) _ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (35 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_35_2 :
    (1386294360849284368221468000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (35 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 2 ⟨(35 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 2 ⟨(35 : Fin 88), complement (htotal3 0 (35 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (35 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (35 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (35 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (35 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42278959891440783148357026710847500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42278959891440783148357026710847500000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 2 ⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84557919782881566296714053421695000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (35 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42278882093222561070450088417950000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 26297888449387912018285946578305000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 2 ⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 26297888449387912018285946578305000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (35 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13149778221817225416934536135210000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(35 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 13148944224693956009142973289152500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 13148944224693956009142973289152500000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 2 ⟨(35 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 26297888449387912018285946578305000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(35 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13148110227570686601351410443095000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84557919782881566296714053421695000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 2 ⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84557919782881566296714053421695000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (35 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42279037689659005226263965003745000000000000000000000000 := by decide +kernel
  have hn : n3 0 (35 : Fin 88) = 110855808232269478315000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (35 : Fin 88)
      ![![0,0],![0,1]] = ((500008225057 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (35 : Fin 88)
      ![![0,0],![1,0]] = ((500008225057 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (35 : Fin 88)
      ![![0,1],![0,0]] = ((499991774943 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (35 : Fin 88)
      ![![1,0],![0,0]] = ((499991774943 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 2) (35 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 2) (35 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_36_1 :
    (1386294361119889560243168000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (36 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(36 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(36 : Fin 88), complement (htotal3 0 (36 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (36 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (36 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (36 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (36 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (36 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (36 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 45723045534459690546981409352632000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 45723045534459690546981409352632000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (36 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22861835432484035145768644500752000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 596754702701598482674477614488004000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 596754702701598482674477614488004000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1193509405403196965348955228976008000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (36 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 596754551486960059362819992181840000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 2220621307131960614752063361671360000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2220621307131960614752063361671360000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (36 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1110310245970988630468629877606744000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(36 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1110310653565980307376031680835680000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1110310653565980307376031680835680000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(36 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2220621307131960614752063361671360000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(36 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (36 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1110311061160971984283433484064616000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1193509405403196965348955228976008000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 1 ⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1193509405403196965348955228976008000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (36 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 596754853916236905986135236794168000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(36 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 22861522767229845273490704676316000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 22861522767229845273490704676316000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 1 ⟨(36 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 45723045534459690546981409352632000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(36 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (36 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22861210101975655401212764851880000000000000000000000000 := by decide +kernel
  have hn : n3 0 (36 : Fin 88) = 3459853758069617270648000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (36 : Fin 88)
      ![![0,0],![0,1]] = ((125000004067 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (36 : Fin 88)
      ![![0,0],![1,0]] = ((125000004067 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (36 : Fin 88)
      ![![0,1],![0,0]] = ((124999995933 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (36 : Fin 88)
      ![![1,0],![0,0]] = ((124999995933 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (36 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (36 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_36_2 :
    (1623444890634254801403647312126 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 2 ⟨(36 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 2 ⟨(36 : Fin 88), complement (htotal3 0 (36 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (36 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (36 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (36 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (36 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (36 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (36 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 45723045534459690546981409352632000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 2 ⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 45723045534459690546981409352632000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (36 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22861835432484035145768644500752000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 596754702701598482674477614488004000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 596754702701598482674477614488004000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 2 ⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1193509405403196965348955228976008000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (36 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 596754551486960059362819992181840000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1110310653565980307376031680835680000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1110310653565980307376031680835680000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 2 ⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2220621307131960614752063361671360000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (36 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1110310245970988630468629877606744000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(36 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 2220621307131960614752063361671360000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 2 ⟨(36 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2220621307131960614752063361671360000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(36 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (36 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1110311061160971984283433484064616000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 56832112361222919059567453516879553277818792000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1079845180680751127229820321942248893444362416000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 56832112361222919059567453516879553277818792000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 2 ⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1193509405403196965348955228976008000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((47617649349 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((452382350651 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((47617649349 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (36 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 596754853916236905986135236794168000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(36 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 22861522767229845273490704676316000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 22861522767229845273490704676316000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 2 ⟨(36 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 45723045534459690546981409352632000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(36 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (36 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22861210101975655401212764851880000000000000000000000000 := by decide +kernel
  have hn : n3 0 (36 : Fin 88) = 3459853758069617270648000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![0,1],![2,2]] = ((1321513087 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![0,2],![1,2]] = ((8213082219102659552109 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![0,2],![2,1]] = ((8213082219102659552109 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![1,0],![2,2]] = ((1321513087 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![1,1],![1,2]] = ((238483170634897340447891 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![1,1],![2,1]] = ((238483170634897340447891 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![1,2],![0,2]] = ((821307805679631230667 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![1,2],![1,1]] = ((23848301328470368769333 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![1,2],![2,0]] = ((821307805679631230667 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![2,0],![1,2]] = ((8213082219102659552109 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![2,0],![2,1]] = ((8213082219102659552109 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![2,1],![0,2]] = ((821307805679631230667 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![2,1],![1,1]] = ((23848301328470368769333 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![2,1],![2,0]] = ((821307805679631230667 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![2,2],![0,1]] = ((3303873087 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88)
      ![![2,2],![1,0]] = ((3303873087 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 2) (36 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 2) (36 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_37_1 :
    (1925701689789338639258579582832 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(37 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(37 : Fin 88), complement (htotal3 0 (37 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (37 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (37 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (37 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (37 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (37 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (37 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (37 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (37 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 0 (37 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 22600263300352215296355845561344000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 22600263300352215296355845561344000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (37 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11299974208301162579333586025032000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1280012176984244494286281605243424000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1280012176984244494286281605243424000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2560024353968488988572563210486848000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (37 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1280012258437935675273746424483184000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 542102721748253283053435093404049819645119008000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9263391272366418181143849546938156360709761984000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 542102721748253283053435093404049819645119008000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 10347596715862924747250719733746256000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((26194619709 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((223805380291 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((26194619709 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (37 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5173798346013130070952735144404280000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 2586569976556095554954176201058104000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2586569976556095554954176201058104000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (37 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1293285073487071473951637336759736000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(37 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 19744546863899785601822185009147448000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 19744546863899785601822185009147448000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 1 ⟨(37 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 39489093727799571203644370018294896000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(37 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (37 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19744546863899785601822185009147448000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(37 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 54547550691167250780473189100857566178868720000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2477474875173761053393229822856388867642262560000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 54547550691167250780473189100857566178868720000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 1 ⟨(37 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 2586569976556095554954176201058104000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(37 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2108875893 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((47891124107 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2108875893 : ℚ)/100000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (37 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1293284903069024081002538864298368000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 10347596715862924747250719733746256000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 1 ⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10347596715862924747250719733746256000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (37 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5173798369849794676297984589341976000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(37 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1280012176984244494286281605243424000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1280012176984244494286281605243424000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 1 ⟨(37 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 2560024353968488988572563210486848000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(37 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (37 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1280012095530553313298816786003664000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 713754258561977393792474224063644769318912000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 21172754783228260508770897113216710461362176000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 713754258561977393792474224063644769318912000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 0 1 ⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 22600263300352215296355845561344000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((15790839449 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((234209160551 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((15790839449 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 0 (37 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11300289092051052717022259536312000000000000000000000000 := by decide +kernel
  have hn : n3 0 (37 : Fin 88) = 35261338173587647107896000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![0,0],![0,2]] = ((4235261993286799146177 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![0,0],![1,1]] = ((41695945903963200853823 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![0,0],![2,0]] = ((4235261993286799146177 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![0,1],![0,1]] = ((632550333401 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![0,1],![1,0]] = ((632550333401 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![0,2],![0,0]] = ((2117631032815223274059 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![1,0],![0,1]] = ((632550333401 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![1,0],![1,0]] = ((632550333401 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![1,1],![0,0]] = ((20847973343434776725941 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88)
      ![![2,0],![0,0]] = ((2117631032815223274059 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (37 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (37 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_37_2 :
    (1044441387587707056586413997586 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 2 ⟨(37 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 2 ⟨(37 : Fin 88), complement (htotal3 0 (37 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (37 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (37 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (37 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (37 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (37 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (37 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (37 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (37 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 0 (37 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 22600263300352215296355845561344000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 2 ⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 22600263300352215296355845561344000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (37 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11299974208301162579333586025032000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1280012176984244494286281605243424000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1280012176984244494286281605243424000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 2 ⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2560024353968488988572563210486848000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (37 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1280012258437935675273746424483184000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 542102721748253283053435093404049819645119008000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9263391272366418181143849546938156360709761984000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 542102721748253283053435093404049819645119008000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 2 ⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 10347596715862924747250719733746256000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((26194619709 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((223805380291 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((26194619709 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (37 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5173798346013130070952735144404280000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1293284988278047777477088100529052000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1293284988278047777477088100529052000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 2 ⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2586569976556095554954176201058104000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (37 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1293285073487071473951637336759736000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(37 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 60518525034642755824617659260364097910758784000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 39368056677730285691995134699774167804178482432000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 60518525034642755824617659260364097910758784000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 2 ⟨(37 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 39489093727799571203644370018294896000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(37 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((191567213 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((62308432787 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((191567213 : ℚ)/125000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (37 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19744546863899785601822185009147448000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(37 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1293284988278047777477088100529052000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1293284988278047777477088100529052000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 2 ⟨(37 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 2586569976556095554954176201058104000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(37 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (37 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1293284903069024081002538864298368000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 541699612978849799912198859686310040985452240000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9264197489905225147426322014373635918029095520000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 541699612978849799912198859686310040985452240000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 2 ⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10347596715862924747250719733746256000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((10470056533 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((89529943467 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10470056533 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (37 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5173798369849794676297984589341976000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(37 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1280012176984244494286281605243424000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1280012176984244494286281605243424000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 2 ⟨(37 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 2560024353968488988572563210486848000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(37 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (37 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1280012095530553313298816786003664000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 22600263300352215296355845561344000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 0 2 ⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 22600263300352215296355845561344000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 0 (37 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11300289092051052717022259536312000000000000000000000000 := by decide +kernel
  have hn : n3 0 (37 : Fin 88) = 35261338173587647107896000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![0,0],![2,2]] = ((320472497 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![0,1],![1,2]] = ((36488929971 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![0,1],![2,1]] = ((36488929971 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![0,2],![0,2]] = ((201535205766680227710181122181807 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![0,2],![1,1]] = ((1826750090241253597315693877818193 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![0,2],![2,0]] = ((201535205766680227710181122181807 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![1,0],![1,2]] = ((36488929971 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![1,0],![2,1]] = ((36488929971 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![1,1],![0,2]] = ((1826750090244545442944193877818193 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![1,1],![1,1]] = ((49482673026185020732029931122181807 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq10 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![1,1],![2,0]] = ((1826750090244545442944193877818193 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq11 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![1,2],![0,1]] = ((14595573879 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq12 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![1,2],![1,0]] = ((14595573879 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq13 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![2,0],![0,2]] = ((201535205766680227710181122181807 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq14 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![2,0],![1,1]] = ((1826750090241253597315693877818193 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq15 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![2,0],![2,0]] = ((201535205766680227710181122181807 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq16 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![2,1],![0,1]] = ((14595573879 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq17 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![2,1],![1,0]] = ((14595573879 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq18 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88)
      ![![2,2],![0,0]] = ((320463567 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 2) (37 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 2) (37 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_38_1 :
    (1178888704256973447694862132814 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(38 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(38 : Fin 88), complement (htotal3 0 (38 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (38 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (38 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (38 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (38 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (38 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (38 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (38 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (38 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 0 (38 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 88524729706041783160165829190977374157744400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2136590089496812109776361888882989251684511200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 88524729706041783160165829190977374157744400000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 2313639548908895676096693547264944000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((1530484379 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((18469515621 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1530484379 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (38 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1156819787896085456125749936481872000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 300513984938491533728551864681752000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 300513984938491533728551864681752000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 601027969876983067457103729363504000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (38 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 300513935048792332317053388674400000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 5429060705671850023401402623664000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 5429060705671850023401402623664000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (38 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2714602032137159938147462359264000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(38 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 339723346412001906267860494191672000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 339723346412001906267860494191672000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(38 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 679446692824003812535720988383344000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(38 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (38 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 339723361179611596143575908895088000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(38 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 158614665475482600307369899998976349761894912000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8654075243909538814647420864731135300476210176000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 158614665475482600307369899998976349761894912000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 1 ⟨(38 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 8971304574860504015262160664729088000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(38 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((17680222999 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((482319777001 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((17680222999 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (38 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4485652287430252007631080332364544000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 339723346412001906267860494191672000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 339723346412001906267860494191672000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 1 ⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 679446692824003812535720988383344000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (38 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 339723331644392216392145079488256000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 5429060705671850023401402623664000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 1 ⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 5429060705671850023401402623664000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (38 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2714458673534690085253940264400000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(38 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 300513984938491533728551864681752000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 300513984938491533728551864681752000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 1 ⟨(38 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 601027969876983067457103729363504000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(38 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (38 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 300514034828190735140050340689104000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 109099702575776155324928777724309548972992416000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2095440143757343365446835991816324902054015168000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 109099702575776155324928777724309548972992416000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 0 1 ⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 2313639548908895676096693547264944000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((23577506407 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((226422493593 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((23577506407 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 0 (38 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1156819761012810219970943610783072000000000000000000000000 := by decide +kernel
  have hn : n3 0 (38 : Fin 88) = 8085195559745806413744000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![0,0],![2,2]] = ((13429279 : ℚ)/40000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![0,1],![1,2]] = ((19796595867 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![0,1],![2,1]] = ((19796595867 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![0,2],![0,2]] = ((344862165095161260975452988939613 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![0,2],![1,1]] = ((5162721029488540763794797011060387 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![0,2],![2,0]] = ((344862165095161260975452988939613 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![1,0],![1,2]] = ((19796595867 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![1,0],![2,1]] = ((19796595867 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![1,1],![0,2]] = ((5162721036880766664338547011060387 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![1,1],![1,1]] = ((94449166690660531310891202988939613 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq10 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![1,1],![2,0]] = ((5162721036880766664338547011060387 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq11 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![1,2],![0,1]] = ((39593183737 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq12 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![1,2],![1,0]] = ((39593183737 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq13 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![2,0],![0,2]] = ((344862165095161260975452988939613 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq14 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![2,0],![1,1]] = ((5162721029488540763794797011060387 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq15 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![2,0],![2,0]] = ((344862165095161260975452988939613 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq16 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![2,1],![0,1]] = ((39593183737 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq17 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![2,1],![1,0]] = ((39593183737 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq18 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88)
      ![![2,2],![0,0]] = ((167874853 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (38 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (38 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1818103397108687862766343975068 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (35 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 0 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 0 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294360849284368221468000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (35 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119889560243168000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (36 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1623444890634254801403647312126 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (36 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1925701689789338639258579582832 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (37 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1044441387587707056586413997586 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (37 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1178888704256973447694862132814 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (38 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_0_35_1, L3C.mx_0_35_2, L3C.mx_0_36_1, L3C.mx_0_36_2, L3C.mx_0_37_1, L3C.mx_0_37_2, L3C.mx_0_38_1⟩
