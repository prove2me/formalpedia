-- Prove2me | solution 1 for mme_released_recursive_level3_mixture101
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T11:26:03.815949+00:00
-- url     : https://prove2.me/submissions/141b49ac-4fe7-4d65-be26-e8a83bd36f56

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

theorem mx_3_80_2 :
    (1897567629643992523213055045078 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(80 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(80 : Fin 88), complement (htotal3 3 (80 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (80 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (80 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (80 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![4,0,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (80 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (80 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (80 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (80 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (80 : Fin 88)) (⟨![4,0,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(80 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 5741579413171382029353112469846000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(80 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 5741579413171382029353112469846000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(80 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2871261758351944469097426286418000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 4991277051580319474339406939188541031835956000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 131101691397144035660737234311824917936328088000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 4991277051580319474339406939188541031835956000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 141084245500304674609416048190202000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((17688995089 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((232311004911 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((17688995089 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 70541518582172376081124656188748000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(80 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 127140574116129644631615419669976000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 127140574116129644631615419669976000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(80 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 254281148232259289263230839339952000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(80 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 127141790880951500763264714267310000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(80 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 127140574116129644631615419669976000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 127140574116129644631615419669976000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(80 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 254281148232259289263230839339952000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(80 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (80 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 127139357351307788499966125072642000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(80 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 141084245500304674609416048190202000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(80 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 141084245500304674609416048190202000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(80 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (80 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 70542726918132298528291392001454000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(80 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 5741579413171382029353112469846000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(80 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = 5741579413171382029353112469846000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(80 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (80 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 2870317654819437560255686183428000000000000000000000000 := by decide +kernel
  have hn : n3 3 (80 : Fin 88) = 401106973145735345902000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![0,0],![0,2]] = ((3110965486920449778353 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![0,0],![1,1]] = ((42645559260829550221647 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![0,0],![2,0]] = ((3110965486920449778353 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![0,1],![0,1]] = ((79243557597 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![0,1],![1,0]] = ((79243557597 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![0,2],![0,0]] = ((1555456099384838590293 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![1,0],![0,1]] = ((79243557597 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![1,0],![1,0]] = ((79243557597 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![1,1],![0,0]] = ((21322723929740161409707 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88)
      ![![2,0],![0,0]] = ((1555456099384838590293 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (80 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (80 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_81_1 :
    (1870916395927886885125277623886 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(81 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(81 : Fin 88), complement (htotal3 3 (81 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (81 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (81 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (81 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (81 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (81 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (81 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (81 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (81 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 3 (81 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 3 (81 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 53422832522952047416081328509360000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 53422832522952047416081328509360000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 106845665045904094832162657018720000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (81 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 53422813008083609125605228079120000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39347177960675049555682011647812087251552000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 651412157911675660986172002592375825496896000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39347177960675049555682011647812087251552000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 730106513833025760097536025888000000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((53892380379 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((446107619621 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((53892380379 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 365053188023113696386935719000880000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 785070881828818519165675442141760000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 785070881828818519165675442141760000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (81 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 392535375207781521231066339150880000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10309276874559835132138091184952000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10309276874559835132138091184952000000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 20618553749119670264276182369904000000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10309276952290775746608236729763360000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 205693755003888396275211174264948807755697920000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10201349549340690260038021156517622384488604160000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 205693755003888396275211174264948807755697920000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 10612737059348467052588443505047520000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((2422722737 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((60077277263 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2422722737 : ℚ)/125000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5306368533419511307380272721293200000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 10612737059348467052588443505047520000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10612737059348467052588443505047520000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5306368525928955745208170783754320000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10309276874559835132138091184952000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10309276874559835132138091184952000000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 20618553749119670264276182369904000000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10309276796828894517667945640140640000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39893101801912184624718604187219950170824640000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 705284678224994149916238233767320099658350720000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39893101801912184624718604187219950170824640000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 785070881828818519165675442141760000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((50814649639 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((449185350361 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((50814649639 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 392535506621036997934609102990880000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 730106513833025760097536025888000000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 730106513833025760097536025888000000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 3 (81 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 365053325809912063710600306887120000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 53422832522952047416081328509360000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 53422832522952047416081328509360000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 3 1 ⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 106845665045904094832162657018720000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 3 (81 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 53422852037820485706557428939600000000000000000000000000 := by decide +kernel
  have hn : n3 3 (81 : Fin 88) = 32853313869175885690960000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![0,0],![0,2]] = ((4336458058749596763137 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![0,0],![1,1]] = ((87951906687250403236863 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![0,0],![2,0]] = ((4336458058749596763137 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![0,1],![0,1]] = ((315423270491 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![0,1],![1,0]] = ((315423270491 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![0,2],![0,0]] = ((4336458040402598281899 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![1,0],![0,1]] = ((315423270491 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![1,0],![1,0]] = ((315423270491 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![1,1],![0,0]] = ((87951906722597401718101 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88)
      ![![2,0],![0,0]] = ((4336458040402598281899 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (81 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (81 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_81_2 :
    (1702306441608677274572600840061 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(81 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(81 : Fin 88), complement (htotal3 3 (81 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (81 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (81 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (81 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (81 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (81 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (81 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (81 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (81 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 3 (81 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc9 : complement (htotal3 3 (81 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 53422832522952047416081328509360000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 53422832522952047416081328509360000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 106845665045904094832162657018720000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (81 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 53422813008083609125605228079120000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39347177960675049555682011647812087251552000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 651412157911675660986172002592375825496896000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39347177960675049555682011647812087251552000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 730106513833025760097536025888000000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((53892380379 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((446107619621 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((53892380379 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 365053188023113696386935719000880000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 392535440914409259582837721070880000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 392535440914409259582837721070880000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 785070881828818519165675442141760000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (81 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 392535375207781521231066339150880000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 20618553749119670264276182369904000000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 20618553749119670264276182369904000000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10309276952290775746608236729763360000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 5306368529674233526294221752523760000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 5306368529674233526294221752523760000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 10612737059348467052588443505047520000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5306368533419511307380272721293200000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 603993979729204819116823026242544432789710880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9404749099890057414354797452562431134420578240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 603993979729204819116823026242544432789710880000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10612737059348467052588443505047520000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((56912177919 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((443087822081 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((56912177919 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5306368525928955745208170783754320000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10309276874559835132138091184952000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10309276874559835132138091184952000000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 20618553749119670264276182369904000000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10309276796828894517667945640140640000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 785070881828818519165675442141760000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 785070881828818519165675442141760000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 392535506621036997934609102990880000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 365053256916512880048768012944000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 365053256916512880048768012944000000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 730106513833025760097536025888000000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 3 (81 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 365053325809912063710600306887120000000000000000000000000 := by decide +kernel
  have hv9 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 106845665045904094832162657018720000000000000000000000000 else 0 := by decide +kernel
  have ht9 : ∑ v, mu3 3 2 ⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 106845665045904094832162657018720000000000000000000000000 := by decide +kernel
  have hf9 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht9, hv9 v]
    split_ifs <;> norm_num
  have hm9 : m3 3 (81 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 53422852037820485706557428939600000000000000000000000000 := by decide +kernel
  have hn : n3 3 (81 : Fin 88) = 32853313869175885690960000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![0,0],![1,2]] = ((13574227563 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![0,0],![2,1]] = ((13574227563 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![0,1],![0,2]] = ((4895557630074017893359 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![0,1],![1,1]] = ((116710886088925982106641 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![0,1],![2,0]] = ((4895557630074017893359 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![0,2],![0,1]] = ((489555751057370795583 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![0,2],![1,0]] = ((489555751057370795583 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![1,0],![0,2]] = ((4895557630074017893359 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![1,0],![1,1]] = ((116710886088925982106641 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![1,0],![2,0]] = ((4895557630074017893359 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq10 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![1,1],![0,1]] = ((11671088628592629204417 : ℚ)/50000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq11 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![1,1],![1,0]] = ((11671088628592629204417 : ℚ)/50000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq12 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![1,2],![0,0]] = ((108593779 : ℚ)/16000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq13 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![2,0],![0,1]] = ((489555751057370795583 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq14 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![2,0],![1,0]] = ((489555751057370795583 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  have hq15 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88)
      ![![2,1],![0,0]] = ((108593779 : ℚ)/16000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (81 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (81 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_82_1 :
    (1846995349746739481365419373707 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(82 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(82 : Fin 88), complement (htotal3 3 (82 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (82 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (82 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (82 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (82 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (82 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (82 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (82 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (82 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4667675659837984101426678676125000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 4667675659837984101426678676125000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2333834100358691321659150918350000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 436357968951039219347025313739700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 436357968951039219347025313739700000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 872715937902078438694050627479400000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 436357839991447962870139210441500000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 278878851191628464744005714728505759614738300000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5501371571795343501562543689279038480770523400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 278878851191628464744005714728505759614738300000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 6059129274178600431050555118736050000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((23013112823 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((226986887177 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((23013112823 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (82 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3029564738793591886312049831946000000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 87091793240374736489483787554212500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 87091793240374736489483787554212500000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 174183586480749472978967575108425000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87091655879495595720171519112275000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 174183586480749472978967575108425000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 1 ⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 174183586480749472978967575108425000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87091930601253877258796055996150000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(82 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 3029564637089300215525277559368025000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3029564637089300215525277559368025000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 1 ⟨(82 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 6059129274178600431050555118736050000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(82 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3029564535385008544738505286790050000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(82 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 18394014438084205552072429287548476773469200000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 835927909025910027589905768904303046453061600000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18394014438084205552072429287548476773469200000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 1 ⟨(82 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 872715937902078438694050627479400000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(82 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((10538374309 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((239461625691 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10538374309 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (82 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 436358097910630475823911417037900000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2333837829918992050713339338062500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2333837829918992050713339338062500000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 1 ⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4667675659837984101426678676125000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (82 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2333841559479292779767527757775000000000000000000000000 := by decide +kernel
  have hn : n3 3 (82 : Fin 88) = 7110696474221266326825000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![0,0],![1,2]] = ((628811573 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![0,0],![2,1]] = ((628811573 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![0,1],![0,2]] = ((5225804038837869571941 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![0,1],![1,1]] = ((55702165322912130428059 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![0,1],![2,0]] = ((5225804038837869571941 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![0,2],![0,1]] = ((2612902279559189373667 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![0,2],![1,0]] = ((2612902279559189373667 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![1,0],![0,2]] = ((5225804038837869571941 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![1,0],![1,1]] = ((55702165322912130428059 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![1,0],![2,0]] = ((5225804038837869571941 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![1,1],![0,1]] = ((27851086456190810626333 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![1,1],![1,0]] = ((27851086456190810626333 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![1,2],![0,0]] = ((6288096937 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![2,0],![0,1]] = ((2612902279559189373667 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![2,0],![1,0]] = ((2612902279559189373667 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88)
      ![![2,1],![0,0]] = ((6288096937 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (82 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (82 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_82_2 :
    (1102315113106241957741561807244 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(82 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(82 : Fin 88), complement (htotal3 3 (82 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (82 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (82 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (82 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (82 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (82 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (82 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (82 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (82 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 4667675659837984101426678676125000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 4667675659837984101426678676125000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2333834100358691321659150918350000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 436357968951039219347025313739700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 436357968951039219347025313739700000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 872715937902078438694050627479400000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 436357839991447962870139210441500000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 278878851191628464744005714728505759614738300000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5501371571795343501562543689279038480770523400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 278878851191628464744005714728505759614738300000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 6059129274178600431050555118736050000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((23013112823 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((226986887177 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((23013112823 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (82 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3029564738793591886312049831946000000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 87091793240374736489483787554212500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 87091793240374736489483787554212500000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 174183586480749472978967575108425000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87091655879495595720171519112275000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 87091793240374736489483787554212500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 87091793240374736489483787554212500000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 174183586480749472978967575108425000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87091930601253877258796055996150000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(82 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1649328519652818341706746537091979895300700000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6055830617139294794367141625661866040209398600000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1649328519652818341706746537091979895300700000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(82 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 6059129274178600431050555118736050000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(82 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((136102767 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((249863897233 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((136102767 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3029564535385008544738505286790050000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(82 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 436357968951039219347025313739700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 436357968951039219347025313739700000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 2 ⟨(82 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 872715937902078438694050627479400000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(82 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (82 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 436358097910630475823911417037900000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4667675659837984101426678676125000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 2 ⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4667675659837984101426678676125000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (82 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2333841559479292779767527757775000000000000000000000000 := by decide +kernel
  have hn : n3 3 (82 : Fin 88) = 7110696474221266326825000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![0,0],![2,2]] = ((328215607 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![0,1],![1,2]] = ((73614413959 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![0,1],![2,1]] = ((73614413959 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![0,2],![0,2]] = ((1334474880293589081538749853257 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![0,2],![1,1]] = ((1231527304355456167718211250146743 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![0,2],![2,0]] = ((1334474880293589081538749853257 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![1,0],![1,2]] = ((73614413959 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![1,0],![2,1]] = ((73614413959 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![1,1],![0,2]] = ((1231527222552987459976211250146743 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![1,1],![1,1]] = ((24164196609273762783224038749853257 : ℚ)/31250000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![1,1],![2,0]] = ((1231527222552987459976211250146743 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![1,2],![0,1]] = ((36807208161 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![1,2],![1,0]] = ((36807208161 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![2,0],![0,2]] = ((1334474880293589081538749853257 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![2,0],![1,1]] = ((1231527304355456167718211250146743 : ℚ)/62500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![2,0],![2,0]] = ((1334474880293589081538749853257 : ℚ)/125000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq16 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![2,1],![0,1]] = ((36807208161 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq17 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![2,1],![1,0]] = ((36807208161 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq18 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88)
      ![![2,2],![0,0]] = ((164107279 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (82 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (82 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_83_1 :
    (1925699747961377067416495514452 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 1 ⟨(83 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 1 ⟨(83 : Fin 88), complement (htotal3 3 (83 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (83 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (83 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (83 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (83 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (83 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (83 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (83 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (83 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 3 (83 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 22302508369587980544284856255760000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 1 ⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 22302508369587980544284856255760000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (83 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11151468881547953646050849658760000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1261942378031274186518201142006600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1261942378031274186518201142006600000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 1 ⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2523884756062548373036402284013200000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (83 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1261942269466189564170934950225360000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 534430551344522587776894529969539762688795520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9132470213736125616367330364550840474622408960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 534430551344522587776894529969539762688795520000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 1 ⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 10201331316425170791921119424489920000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((26194157153 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((223805842847 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((26194157153 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (83 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5100665653901964040478311550931840000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 2549950764308879995639186327966680000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 1 ⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2549950764308879995639186327966680000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (83 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1274975275449179911910232428897680000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(83 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 19465606102271298030739007107274440000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 19465606102271298030739007107274440000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 1 ⟨(83 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 38931212204542596061478014214548880000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(83 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19465606102271298030739007107274440000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(83 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 53775743297810953676997568410655265208086280000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2442399277713258088285191191145369469583827440000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 53775743297810953676997568410655265208086280000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 1 ⟨(83 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 2549950764308879995639186327966680000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(83 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((21088933971 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((478911066029 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((21088933971 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1274975488859700083728953899069000000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 10201331316425170791921119424489920000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 1 ⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10201331316425170791921119424489920000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5100665662523206751442807873558080000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(83 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1261942378031274186518201142006600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1261942378031274186518201142006600000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 1 ⟨(83 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 2523884756062548373036402284013200000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(83 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1261942486596358808865467333787840000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 1 ⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 704457161502870799139282641026056633046800000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 20893594046582238946006290973707886733906400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 704457161502870799139282641026056633046800000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 3 1 ⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 22302508369587980544284856255760000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 1) ⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((6317290861 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((93682709139 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((6317290861 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 3 (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11151039488040026898234006597000000000000000000000000000 := by decide +kernel
  have hn : n3 3 (83 : Fin 88) = 34763075447437485171880000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![0,0],![0,2]] = ((8470348980031305360187 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![0,0],![1,1]] = ((83391379659468694639813 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![0,0],![2,0]] = ((8470348980031305360187 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![0,1],![0,1]] = ((632553091903 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![0,1],![1,0]] = ((632553091903 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![0,2],![0,0]] = ((2117587176587021371227 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![1,0],![0,1]] = ((632553091903 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![1,0],![1,0]] = ((632553091903 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![1,1],![0,0]] = ((20847844175662978628773 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88)
      ![![2,0],![0,0]] = ((2117587176587021371227 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 1) (83 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 1) (83 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_3_83_2 :
    (1044466180089203792700595785619 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 3 2 ⟨(83 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 3 2 ⟨(83 : Fin 88), complement (htotal3 3 (83 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 3 (83 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 3 (83 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 3 (83 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 3 (83 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 3 (83 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 3 (83 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 3 (83 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 3 (83 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 3 (83 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 22302508369587980544284856255760000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 3 2 ⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 22302508369587980544284856255760000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 3 (83 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11151468881547953646050849658760000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1261942378031274186518201142006600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1261942378031274186518201142006600000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 3 2 ⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2523884756062548373036402284013200000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 3 (83 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1261942269466189564170934950225360000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 534430551344522587776894529969539762688795520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9132470213736125616367330364550840474622408960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 534430551344522587776894529969539762688795520000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 3 2 ⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 10201331316425170791921119424489920000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((26194157153 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((223805842847 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((26194157153 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 3 (83 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5100665653901964040478311550931840000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1274975382154439997819593163983340000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1274975382154439997819593163983340000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 3 2 ⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 2549950764308879995639186327966680000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 3 (83 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1274975275449179911910232428897680000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(83 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 59791765491155775192390544659995887010446000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 38811628673560284511093233125228888225979108000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 59791765491155775192390544659995887010446000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 3 2 ⟨(83 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 38931212204542596061478014214548880000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(83 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((61433243 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((19938566757 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((61433243 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 3 (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19465606102271298030739007107274440000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(83 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1274975382154439997819593163983340000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1274975382154439997819593163983340000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 3 2 ⟨(83 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 2549950764308879995639186327966680000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(83 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 3 (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1274975488859700083728953899069000000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 534031190880910927111028409392607520512895680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9133268934663348937699062605704704958974208640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 534031190880910927111028409392607520512895680000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 3 2 ⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 10201331316425170791921119424489920000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((52349166429 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((447650833571 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((52349166429 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 3 (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5100665662523206751442807873558080000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(83 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1261942378031274186518201142006600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1261942378031274186518201142006600000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 3 2 ⟨(83 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 2523884756062548373036402284013200000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(83 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 3 (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1261942486596358808865467333787840000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 3 2 ⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 22302508369587980544284856255760000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 3 2 ⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 22302508369587980544284856255760000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 3 2) ⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 3 (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11151039488040026898234006597000000000000000000000000000 := by decide +kernel
  have hn : n3 3 (83 : Fin 88) = 34763075447437485171880000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![0,0],![2,2]] = ((12830901 : ℚ)/40000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![0,1],![1,2]] = ((72977374493 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![0,1],![2,1]] = ((72977374493 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![0,2],![0,2]] = ((806111327669587120317754385017741 : ℚ)/1000000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![0,2],![1,1]] = ((7307767358223691091605745614982259 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![0,2],![2,0]] = ((806111327669587120317754385017741 : ℚ)/1000000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![1,0],![1,2]] = ((72977374493 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![1,0],![2,1]] = ((72977374493 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![1,1],![0,2]] = ((7307767358228545428353745614982259 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![1,1],![1,1]] = ((197929280455128176359722754385017741 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq10 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![1,1],![2,0]] = ((7307767358228545428353745614982259 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq11 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![1,2],![0,1]] = ((18244340527 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq12 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![1,2],![1,0]] = ((18244340527 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq13 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![2,0],![0,2]] = ((806111327669587120317754385017741 : ℚ)/1000000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq14 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![2,0],![1,1]] = ((7307767358223691091605745614982259 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq15 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![2,0],![2,0]] = ((806111327669587120317754385017741 : ℚ)/1000000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq16 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![2,1],![0,1]] = ((18244340527 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq17 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![2,1],![1,0]] = ((18244340527 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq18 : mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88)
      ![![2,2],![0,0]] = ((320784877 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 3) (n3 3) (m3 3)
      (mu3 3 2) (83 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 3) (n3 3) (m3 3)
        (mu3 3 2) (83 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1897567629643992523213055045078 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (80 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1870916395927886885125277623886 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (81 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1702306441608677274572600840061 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (81 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1846995349746739481365419373707 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (82 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1102315113106241957741561807244 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (82 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1925699747961377067416495514452 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 1) (83 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 3 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1044466180089203792700595785619 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (83 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_3_80_2, L3C.mx_3_81_1, L3C.mx_3_81_2, L3C.mx_3_82_1, L3C.mx_3_82_2, L3C.mx_3_83_1, L3C.mx_3_83_2⟩
