-- Prove2me | solution 1 for mme_released_recursive_level3_mixture82
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T21:16:01.937901+00:00
-- url     : https://prove2.me/submissions/c6e72c23-d63e-494c-9b8b-89cad3b2208d

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

theorem mx_3_14_1 :
    (1810281995484683818039509351568 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(14 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(14 : Fin 88), complement (htotal3 3 (14 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,2],![2,2]] + g ![![1,1],![2,2]] + g ![![1,2],![1,2]] + g ![![1,2],![2,1]] + g ![![2,0],![2,2]] + g ![![2,1],![1,2]] + g ![![2,1],![2,1]] + g ![![2,2],![0,2]] + g ![![2,2],![1,1]] + g ![![2,2],![2,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (14 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (14 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (14 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (14 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(14 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42222674313102553140270722870100000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42222674313102553140270722870100000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(14 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84445348626205106280541445740200000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(14 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (14 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42210961169391307424916008580600000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25808681866625590319458554259800000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25808681866625590319458554259800000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (14 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12907949612284560361981367989200000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(14 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 463866571701991077326394871596899192587800000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 24880948723221608164805764516606201614824400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 463866571701991077326394871596899192587800000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(14 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25808681866625590319458554259800000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(14 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((17973276361 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((482026723639 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((17973276361 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (14 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12900732254341029957477186270600000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42222674313102553140270722870100000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42222674313102553140270722870100000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84445348626205106280541445740200000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (14 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42234387456813798855625437159600000000000000000000000000 := by decide +kernel
  have hn : n3 3 (14 : Fin 88) = 110254030492830696600000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![0,2],![2,2]] = ((2103038093302314163651 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![1,1],![2,2]] = ((56401545352197685836349 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![1,2],![1,2]] = ((765916205047 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![1,2],![2,1]] = ((765916205047 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![2,0],![2,2]] = ((2103038093302314163651 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![2,1],![1,2]] = ((765916205047 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![2,1],![2,1]] = ((765916205047 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![2,2],![0,2]] = ((1052107322509805921191 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![2,2],![1,1]] = ((28216549692990194078809 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88)
      ![![2,2],![2,0]] = ((1052107322509805921191 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (14 : Fin 88)) _ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (14 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_14_2 :
    (1386294321278297593425805811454 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (14 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(14 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(14 : Fin 88), complement (htotal3 3 (14 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (14 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (14 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (14 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (14 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(14 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42222674313102553140270722870100000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42222674313102553140270722870100000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(14 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84445348626205106280541445740200000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(14 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (14 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42210961169391307424916008580600000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25808681866625590319458554259800000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25808681866625590319458554259800000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (14 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12907949612284560361981367989200000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(14 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12904340933312795159729277129900000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12904340933312795159729277129900000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(14 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25808681866625590319458554259800000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(14 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (14 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12900732254341029957477186270600000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84445348626205106280541445740200000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84445348626205106280541445740200000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (14 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42234387456813798855625437159600000000000000000000000000 := by decide +kernel
  have hn : n3 3 (14 : Fin 88) = 110254030492830696600000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (14 : Fin 88)
      ![![0,0],![0,1]] = ((31258685523 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (14 : Fin 88)
      ![![0,0],![1,0]] = ((31258685523 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (14 : Fin 88)
      ![![0,1],![0,0]] = ((31241314477 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (14 : Fin 88)
      ![![1,0],![0,0]] = ((31241314477 : ℚ)/125000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (14 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (14 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_15_1 :
    (1644692429799104767422524119431 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(15 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(15 : Fin 88), complement (htotal3 3 (15 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (15 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (15 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (15 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (15 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (15 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (15 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 362119442210110110004528122532665000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 362119442210110110004528122532665000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 724238884420220220009056245065330000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (15 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 362119431065978804031495483381798000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 29098658919690281986880164929318000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 29098658919690281986880164929318000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14549342842932796909668037115088000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(15 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 7952264519925586929788577685584139367400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1314011602863455293644204012849980831721265200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 7952264519925586929788577685584139367400000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(15 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1314027507392495144818063590005352000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(15 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((242073 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((19999757927 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((242073 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (15 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 657013764152979999013539556587888000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 657013753696247572409031795002676000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 657013753696247572409031795002676000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 1314027507392495144818063590005352000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 657013743239515145804524033417464000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(15 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 14549329459845140993440082464659000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 14549329459845140993440082464659000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 1 ⟨(15 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 29098658919690281986880164929318000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(15 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (15 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14549316076757485077212127814230000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 38504483456454819565346946609930661276225950000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 647229917507310580878362351845468677447548100000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 38504483456454819565346946609930661276225950000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 1 ⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 724238884420220220009056245065330000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((10633089243 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((89366910757 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10633089243 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (15 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 362119453354241415977560761683532000000000000000000000000 := by decide +kernel
  have hn : n3 3 (15 : Fin 88) = 2067365050732405646814000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![0,1],![2,2]] = ((1407522689 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![0,2],![1,2]] = ((931437747107675337507 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![0,2],![2,1]] = ((931437747107675337507 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![1,0],![2,2]] = ((1407522689 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![1,1],![1,2]] = ((23716681779392324662493 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![1,1],![2,1]] = ((23716681779392324662493 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![1,2],![0,2]] = ((1862875379567771493891 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![1,2],![1,1]] = ((47433361583732228506109 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![1,2],![2,0]] = ((1862875379567771493891 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![2,0],![1,2]] = ((931437747107675337507 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![2,0],![2,1]] = ((931437747107675337507 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![2,1],![0,2]] = ((1862875379567771493891 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![2,1],![1,1]] = ((47433361583732228506109 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![2,1],![2,0]] = ((1862875379567771493891 : ℚ)/400000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![2,2],![0,1]] = ((879703299 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88)
      ![![2,2],![1,0]] = ((879703299 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (15 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (15 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_15_2 :
    (1386294361119890433547920000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (15 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(15 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(15 : Fin 88), complement (htotal3 3 (15 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (15 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (15 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (15 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (15 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (15 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (15 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 362119442210110110004528122532665000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 362119442210110110004528122532665000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 724238884420220220009056245065330000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (15 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 362119431065978804031495483381798000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 29098658919690281986880164929318000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 29098658919690281986880164929318000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14549342842932796909668037115088000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(15 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 657013753696247572409031795002676000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 657013753696247572409031795002676000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(15 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1314027507392495144818063590005352000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(15 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (15 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 657013764152979999013539556587888000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1314027507392495144818063590005352000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 1314027507392495144818063590005352000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 657013743239515145804524033417464000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(15 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 14549329459845140993440082464659000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 14549329459845140993440082464659000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(15 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 29098658919690281986880164929318000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(15 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (15 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14549316076757485077212127814230000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 724238884420220220009056245065330000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 724238884420220220009056245065330000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (15 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 362119453354241415977560761683532000000000000000000000000 := by decide +kernel
  have hn : n3 3 (15 : Fin 88) = 2067365050732405646814000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (15 : Fin 88)
      ![![0,0],![0,1]] = ((250000003403 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (15 : Fin 88)
      ![![0,0],![1,0]] = ((250000003403 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (15 : Fin 88)
      ![![0,1],![0,0]] = ((249999996597 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (15 : Fin 88)
      ![![1,0],![0,0]] = ((249999996597 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (15 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (15 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_16_1 :
    (1123569606463069574750240901251 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(16 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(16 : Fin 88), complement (htotal3 3 (16 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (16 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (16 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (16 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (16 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (16 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (16 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (16 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (16 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 408035792340916514449245520171645500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 408035792340916514449245520171645500000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 816071584681833028898491040343291000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (16 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 408035279665218988138123117012068000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 21603271001362594510708163911608000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 21603271001362594510708163911608000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10801584124758690326696002081383000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(16 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 34295846637495374662793167263908104395665625000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 28257171850249088425645006961928508791208668750000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 34295846637495374662793167263908104395665625000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(16 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 28325763543524079174970593296456325000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(16 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((9686121 : ℚ)/8000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((3990313879 : ℚ)/4000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((9686121 : ℚ)/8000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (16 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 14162882163882684455357724945725244000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2087950692326491763650603749644388000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2087950692326491763650603749644388000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4175901384652983527301207499288776000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2087951095299091731169546132150635000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(16 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 2087950692326491763650603749644388000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2087950692326491763650603749644388000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 1 ⟨(16 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 4175901384652983527301207499288776000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(16 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (16 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2087950289353891796131661367138141000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1333753522564481711567498288433948953315191650000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25658256498395115751835596719588427093369616700000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1333753522564481711567498288433948953315191650000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 1 ⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 28325763543524079174970593296456325000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((23543116861 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((226456883139 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((23543116861 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (16 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 14162881379641394719612868350731081000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(16 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 21603271001362594510708163911608000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 1 ⟨(16 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 21603271001362594510708163911608000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(16 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (16 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10801686876603904184012161830225000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 408035792340916514449245520171645500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 408035792340916514449245520171645500000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 1 ⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 816071584681833028898491040343291000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (16 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 408036305016614040760367923331223000000000000000000000000 := by decide +kernel
  have hn : n3 3 (16 : Fin 88) = 33339339783860258325681000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![0,0],![2,2]] = ((12959689 : ℚ)/40000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![0,1],![1,2]] = ((18716526861 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![0,1],![2,1]] = ((18716526861 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![0,2],![0,2]] = ((7749942312888813417100044753 : ℚ)/160000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![0,2],![1,1]] = ((1633613494508160622104659955247 : ℚ)/80000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![0,2],![2,0]] = ((7749942312888813417100044753 : ℚ)/160000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![1,0],![1,2]] = ((18716526861 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![1,0],![2,1]] = ((18716526861 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![1,1],![0,2]] = ((1633613580838452446683139955247 : ℚ)/80000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![1,1],![1,1]] = ((30709815395340498117795100044753 : ℚ)/40000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![1,1],![2,0]] = ((1633613580838452446683139955247 : ℚ)/80000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![1,2],![0,1]] = ((74866100863 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![1,2],![1,0]] = ((74866100863 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![2,0],![0,2]] = ((7749942312888813417100044753 : ℚ)/160000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![2,0],![1,1]] = ((1633613494508160622104659955247 : ℚ)/80000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![2,0],![2,0]] = ((7749942312888813417100044753 : ℚ)/160000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq16 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![2,1],![0,1]] = ((74866100863 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq17 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![2,1],![1,0]] = ((74866100863 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq18 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88)
      ![![2,2],![0,0]] = ((323989143 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (16 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (16 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_16_2 :
    (1386294361119889816585488000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (16 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(16 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(16 : Fin 88), complement (htotal3 3 (16 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (16 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (16 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (16 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (16 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (16 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (16 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (16 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (16 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 408035792340916514449245520171645500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 408035792340916514449245520171645500000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 816071584681833028898491040343291000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (16 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 408035279665218988138123117012068000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 21603271001362594510708163911608000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 21603271001362594510708163911608000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10801584124758690326696002081383000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(16 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 14162881771762039587485296648228162500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 14162881771762039587485296648228162500000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(16 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 28325763543524079174970593296456325000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(16 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (16 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 14162882163882684455357724945725244000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4175901384652983527301207499288776000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4175901384652983527301207499288776000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2087951095299091731169546132150635000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(16 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 2087950692326491763650603749644388000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2087950692326491763650603749644388000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(16 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 4175901384652983527301207499288776000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(16 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (16 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2087950289353891796131661367138141000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 28325763543524079174970593296456325000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 28325763543524079174970593296456325000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (16 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 14162881379641394719612868350731081000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(16 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10801635500681297255354081955804000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10801635500681297255354081955804000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 2 ⟨(16 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 21603271001362594510708163911608000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(16 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (16 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10801686876603904184012161830225000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 816071584681833028898491040343291000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 2 ⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 816071584681833028898491040343291000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (16 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 408036305016614040760367923331223000000000000000000000000 := by decide +kernel
  have hn : n3 3 (16 : Fin 88) = 33339339783860258325681000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (16 : Fin 88)
      ![![0,0],![0,1]] = ((250000007081 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (16 : Fin 88)
      ![![0,0],![1,0]] = ((250000007081 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (16 : Fin 88)
      ![![0,1],![0,0]] = ((249999992919 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (16 : Fin 88)
      ![![1,0],![0,0]] = ((249999992919 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (16 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (16 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_17_1 :
    (1386293926546801293953988494874 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (17 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(17 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(17 : Fin 88), complement (htotal3 3 (17 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (17 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (17 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (17 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (17 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(17 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12558752483084756054953689635240000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12558752483084756054953689635240000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(17 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 25117504966169512109907379270480000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(17 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (17 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12511948826738998084376192705840000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(17 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84482294228396880770092620729520000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(17 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 84482294228396880770092620729520000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(17 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (17 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42245430285365743858733983249200000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42241147114198440385046310364760000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42241147114198440385046310364760000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 84482294228396880770092620729520000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (17 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42236863943031136911358637480320000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25117504966169512109907379270480000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 25117504966169512109907379270480000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (17 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12605556139430514025531186564640000000000000000000000000 := by decide +kernel
  have hn : n3 3 (17 : Fin 88) = 109599799194566392880000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (17 : Fin 88)
      ![![0,0],![0,1]] = ((500466121543 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (17 : Fin 88)
      ![![0,0],![1,0]] = ((500466121543 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (17 : Fin 88)
      ![![0,1],![0,0]] = ((499533878457 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (17 : Fin 88)
      ![![1,0],![0,0]] = ((499533878457 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (17 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (17 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1810281995484683818039509351568 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (14 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294321278297593425805811454 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (14 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1644692429799104767422524119431 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (15 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119890433547920000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (15 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1123569606463069574750240901251 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (16 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119889816585488000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (16 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386293926546801293953988494874 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (17 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_3_14_1, L3C.mx_3_14_2, L3C.mx_3_15_1, L3C.mx_3_15_2, L3C.mx_3_16_1, L3C.mx_3_16_2, L3C.mx_3_17_1⟩
