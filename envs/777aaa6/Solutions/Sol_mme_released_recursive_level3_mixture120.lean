-- Prove2me | solution 1 for mme_released_recursive_level3_mixture120
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T14:20:51.798868+00:00
-- url     : https://prove2.me/submissions/a71dd9d3-a669-45a1-931f-668f57e6a735

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

theorem mx_4_56_1 :
    (1765456678143410859993413502894 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-55 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-55 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 1 ⟨(56 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 1 ⟨(56 : Fin 88), complement (htotal3 4 (56 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,2],![2,2]] + g ![![1,1],![2,2]] + g ![![1,2],![1,2]] + g ![![1,2],![2,1]] + g ![![2,0],![2,2]] + g ![![2,1],![1,2]] + g ![![2,1],![2,1]] + g ![![2,2],![0,2]] + g ![![2,2],![1,1]] + g ![![2,2],![2,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (56 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (56 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (56 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (56 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(56 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42293891150176817819845681940750000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42293891150176817819845681940750000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 1 ⟨(56 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84587782300353635639691363881500000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(56 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (56 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42316252933769520577467087970000000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(56 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25072211825717094860308636118500000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 1 ⟨(56 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25072211825717094860308636118500000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(56 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (56 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12543069868647153666436341314500000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(56 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 71096619196678497250910831416691369000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25072069632478701503314134296837166617262000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 71096619196678497250910831416691369000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 1 ⟨(56 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25072211825717094860308636118500000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(56 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((1417837 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((249998582163 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1417837 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (56 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12529141957069941193872294804000000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(56 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42293891150176817819845681940750000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42293891150176817819845681940750000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 1 ⟨(56 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84587782300353635639691363881500000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(56 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (56 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42271529366584115062224275911500000000000000000000000000 := by decide +kernel
  have hn : n3 4 (56 : Fin 88) = 109659994126070730500000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![0,2],![2,2]] = ((20249272748185917 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![1,1],![2,2]] = ((3570431210977251814083 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![1,2],![1,2]] = ((771364096583 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![1,2],![2,1]] = ((771364096583 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq4 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![2,0],![2,2]] = ((20249272748185917 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq5 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![2,1],![1,2]] = ((771364096583 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq6 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![2,1],![2,1]] = ((771364096583 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq7 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![2,2],![0,2]] = ((162174261407561693 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq8 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![2,2],![1,1]] = ((28595201997988592438307 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq9 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88)
      ![![2,2],![2,0]] = ((162174261407561693 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 1) (56 : Fin 88)) _ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 1) (56 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_56_2 :
    (1386294320323518558705650954328 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (56 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 2 ⟨(56 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 2 ⟨(56 : Fin 88), complement (htotal3 4 (56 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (56 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (56 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (56 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (56 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(56 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42293891150176817819845681940750000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42293891150176817819845681940750000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 2 ⟨(56 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84587782300353635639691363881500000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(56 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (56 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42316252933769520577467087970000000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(56 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25072211825717094860308636118500000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 2 ⟨(56 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25072211825717094860308636118500000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(56 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (56 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12543069868647153666436341314500000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(56 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12536105912858547430154318059250000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12536105912858547430154318059250000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 2 ⟨(56 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25072211825717094860308636118500000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(56 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (56 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12529141957069941193872294804000000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(56 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84587782300353635639691363881500000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 2 ⟨(56 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84587782300353635639691363881500000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(56 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (56 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42271529366584115062224275911500000000000000000000000000 := by decide +kernel
  have hn : n3 4 (56 : Fin 88) = 109659994126070730500000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (56 : Fin 88)
      ![![0,0],![0,1]] = ((124964896433 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (56 : Fin 88)
      ![![0,0],![1,0]] = ((124964896433 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (56 : Fin 88)
      ![![0,1],![0,0]] = ((125035103567 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (56 : Fin 88)
      ![![1,0],![0,0]] = ((125035103567 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 2) (56 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 2) (56 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_57_1 :
    (1386294361119652357700064000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (57 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 1 ⟨(57 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 1 ⟨(57 : Fin 88), complement (htotal3 4 (57 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (57 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (57 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (57 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (57 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(57 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 13129827156079812392569288774596000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 13129827156079812392569288774596000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 1 ⟨(57 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 26259654312159624785138577549192000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(57 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13129833437108656345036039771512000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84528592132833968028861422450808000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 1 ⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 84528592132833968028861422450808000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42264275308466400601761200037480000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(57 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42264296066416984014430711225404000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42264296066416984014430711225404000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 1 ⟨(57 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 84528592132833968028861422450808000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(57 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42264316824367567427100222413328000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 26259654312159624785138577549192000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 1 ⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 26259654312159624785138577549192000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (57 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13129820875050968440102537777680000000000000000000000000 := by decide +kernel
  have hn : n3 4 (57 : Fin 88) = 110788246444993592814000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (57 : Fin 88)
      ![![0,0],![0,1]] = ((24999987797 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (57 : Fin 88)
      ![![0,0],![1,0]] = ((24999987797 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (57 : Fin 88)
      ![![0,1],![0,0]] = ((25000012203 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (57 : Fin 88)
      ![![1,0],![0,0]] = ((25000012203 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 1) (57 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 1) (57 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_57_2 :
    (1386294361119822318148128000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (57 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 2 ⟨(57 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 2 ⟨(57 : Fin 88), complement (htotal3 4 (57 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (57 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (57 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (57 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (57 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(57 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 13129827156079812392569288774596000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 13129827156079812392569288774596000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 2 ⟨(57 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 26259654312159624785138577549192000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(57 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13129833437108656345036039771512000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42264296066416984014430711225404000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42264296066416984014430711225404000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 2 ⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 84528592132833968028861422450808000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42264275308466400601761200037480000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(57 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84528592132833968028861422450808000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 2 ⟨(57 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 84528592132833968028861422450808000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(57 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42264316824367567427100222413328000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 26259654312159624785138577549192000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 2 ⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 26259654312159624785138577549192000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (57 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13129820875050968440102537777680000000000000000000000000 := by decide +kernel
  have hn : n3 4 (57 : Fin 88) = 110788246444993592814000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (57 : Fin 88)
      ![![0,0],![0,1]] = ((31250008167 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (57 : Fin 88)
      ![![0,0],![1,0]] = ((31250008167 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (57 : Fin 88)
      ![![0,1],![0,0]] = ((31249991833 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (57 : Fin 88)
      ![![1,0],![0,0]] = ((31249991833 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 2) (57 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 2) (57 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_58_1 :
    (1386294361119889374861564000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (58 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 1 ⟨(58 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 1 ⟨(58 : Fin 88), complement (htotal3 4 (58 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (58 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (58 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (58 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (58 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (58 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (58 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(58 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 6769098288670753436586210863194500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 6769098288670753436586210863194500000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 1 ⟨(58 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 13538196577341506873172421726389000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(58 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (58 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6769109057393498138798175969840000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 327462509189550912596982571417695000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 1 ⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 327462509189550912596982571417695000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (58 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 163731251819226549759043018621059000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(58 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 292014045806680147053422503427958000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 292014045806680147053422503427958000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 1 ⟨(58 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 584028091613360294106845006855916000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(58 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 292014015949525654011005667303129000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 584028091613360294106845006855916000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 1 ⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 584028091613360294106845006855916000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 292014075663834640095839339552787000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(58 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 163731254594775456298491285708847500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 163731254594775456298491285708847500000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 1 ⟨(58 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 327462509189550912596982571417695000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(58 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 163731257370324362837939552796636000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(58 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 13538196577341506873172421726389000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 1 ⟨(58 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 13538196577341506873172421726389000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(58 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (58 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6769087519948008734374245756549000000000000000000000000 := by decide +kernel
  have hn : n3 4 (58 : Fin 88) = 925028797380252713577000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (58 : Fin 88)
      ![![0,0],![0,1]] = ((100000003527 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (58 : Fin 88)
      ![![0,0],![1,0]] = ((100000003527 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (58 : Fin 88)
      ![![0,1],![0,0]] = ((99999996473 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (58 : Fin 88)
      ![![1,0],![0,0]] = ((99999996473 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 1) (58 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 1) (58 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_58_2 :
    (1903205944219358882390249771802 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 2 ⟨(58 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 2 ⟨(58 : Fin 88), complement (htotal3 4 (58 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (58 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (58 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (58 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (58 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (58 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (58 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(58 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 13538196577341506873172421726389000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 2 ⟨(58 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 13538196577341506873172421726389000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(58 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (58 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6769109057393498138798175969840000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 12334552595854038967219784510853452825576880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 302793403997842834662543002395988094348846240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 12334552595854038967219784510853452825576880000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 2 ⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 327462509189550912596982571417695000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2354191749 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((28895808251 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2354191749 : ℚ)/62500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (58 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 163731251819226549759043018621059000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(58 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 292014045806680147053422503427958000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 292014045806680147053422503427958000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 2 ⟨(58 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 584028091613360294106845006855916000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(58 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 292014015949525654011005667303129000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 292014045806680147053422503427958000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 292014045806680147053422503427958000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 2 ⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 584028091613360294106845006855916000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 292014075663834640095839339552787000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(58 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 327462509189550912596982571417695000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 2 ⟨(58 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 327462509189550912596982571417695000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(58 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 163731257370324362837939552796636000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(58 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 13538196577341506873172421726389000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 2 ⟨(58 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 13538196577341506873172421726389000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(58 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (58 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6769087519948008734374245756549000000000000000000000000 := by decide +kernel
  have hn : n3 4 (58 : Fin 88) = 925028797380252713577000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![0,0],![0,2]] = ((104173723090094158683 : ℚ)/15625000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![0,0],![1,1]] = ((1335818143355218341317 : ℚ)/7812500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![0,0],![2,0]] = ((104173723090094158683 : ℚ)/15625000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![0,1],![0,1]] = ((157840516227 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![0,1],![1,0]] = ((157840516227 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![0,2],![0,0]] = ((416694878232871948983 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![1,0],![0,1]] = ((157840516227 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![1,0],![1,0]] = ((157840516227 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![1,1],![0,0]] = ((5343273127610878051017 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88)
      ![![2,0],![0,0]] = ((416694878232871948983 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 2) (58 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 2) (58 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_59_1 :
    (1386294361119883165274908000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (59 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 1 ⟨(59 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 1 ⟨(59 : Fin 88), complement (htotal3 4 (59 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (59 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (59 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (59 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (59 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (59 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (59 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (59 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (59 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 4 (59 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 4 (59 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(59 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 860494279805507483319599903475000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 1 ⟨(59 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 860494279805507483319599903475000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(59 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (59 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 430225497051953408115910729731000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(59 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 16032130774617611585307532486239000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 16032130774617611585307532486239000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 1 ⟨(59 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 32064261549235223170615064972478000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(59 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (59 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 16032073592338539622702044499269000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(59 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 162816894238979943788961218762628000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 1 ⟨(59 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 162816894238979943788961218762628000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(59 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (59 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 81408497625430281578647201582719000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(59 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 563807942287936035007052058180709500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 563807942287936035007052058180709500000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 1 ⟨(59 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 1127615884575872070014104116361419000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(59 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (59 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 563807971207929918347362149171759000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(59 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1127615884575872070014104116361419000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 1 ⟨(59 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1127615884575872070014104116361419000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(59 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (59 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 563807913367942151666741967189660000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(59 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 81408447119489971894480609381314000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 81408447119489971894480609381314000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 1 ⟨(59 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 162816894238979943788961218762628000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(59 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 81408396613549662210314017179909000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(59 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 32064261549235223170615064972478000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 4 1 ⟨(59 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 32064261549235223170615064972478000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(59 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 4 (59 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 16032187956896683547913020473209000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(59 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 430247139902753741659799951737500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 430247139902753741659799951737500000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 4 1 ⟨(59 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 860494279805507483319599903475000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(59 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 4 (59 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 430268782753554075203689173744000000000000000000000000 := by decide +kernel
  have hn : n3 4 (59 : Fin 88) = 1323357534643892744457000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (59 : Fin 88)
      ![![0,0],![0,1]] = ((500000043167 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (59 : Fin 88)
      ![![0,0],![1,0]] = ((500000043167 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (59 : Fin 88)
      ![![0,1],![0,0]] = ((499999956833 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (59 : Fin 88)
      ![![1,0],![0,0]] = ((499999956833 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 1) (59 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 1) (59 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1765456678143410859993413502894 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (56 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-55 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-55 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294320323518558705650954328 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (56 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119652357700064000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (57 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119822318148128000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (57 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119889374861564000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (58 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1903205944219358882390249771802 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (58 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119883165274908000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (59 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_4_56_1, L3C.mx_4_56_2, L3C.mx_4_57_1, L3C.mx_4_57_2, L3C.mx_4_58_1, L3C.mx_4_58_2, L3C.mx_4_59_1⟩
