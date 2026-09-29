-- Prove2me | solution 1 for mme_released_recursive_level3_mixture115
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T13:47:57.668756+00:00
-- url     : https://prove2.me/submissions/ec1cae3d-cf27-4f1a-be11-30c43b57c861

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

theorem mx_4_38_2 :
    (1386294361119889816358880000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (38 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 2 ⟨(38 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 2 ⟨(38 : Fin 88), complement (htotal3 4 (38 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (38 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (38 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (38 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![3,1,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (38 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![3,0,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (38 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (38 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (38 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (38 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 4 (38 : Fin 88)) (⟨![3,0,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 4 (38 : Fin 88)) (⟨![3,1,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 405084877872303647269707686902815000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 405084877872303647269707686902815000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 2 ⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 810169755744607294539415373805630000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (38 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 405085390472394163445829530907864000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 21448036035833986999198416871662000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 2 ⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 21448036035833986999198416871662000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (38 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10723986060057735864365576537928000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(38 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 14061110549878067160345263864976801000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 14061110549878067160345263864976801000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 2 ⟨(38 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 28122221099756134320690527729953602000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(38 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (38 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 14061110126150946200617202405897562000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4145963550343521375396858479369106000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 2 ⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 4145963550343521375396858479369106000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (38 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2072981427176987714992029665413602000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(38 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 2072981775171760687698429239684553000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2072981775171760687698429239684553000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 2 ⟨(38 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 4145963550343521375396858479369106000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(38 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (38 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2072982123166533660404828813955504000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 28122221099756134320690527729953602000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 2 ⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 28122221099756134320690527729953602000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (38 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 14061110973605188120073325324056040000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10724018017916993499599208435831000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10724018017916993499599208435831000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 4 2 ⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = 21448036035833986999198416871662000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 4 (38 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10724049975776251134832840333734000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 810169755744607294539415373805630000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 4 2 ⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = 810169755744607294539415373805630000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 4 (38 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 405084365272213131093585842897766000000000000000000000000 := by decide +kernel
  have hn : n3 4 (38 : Fin 88) = 33099802441880096977626000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (38 : Fin 88)
      ![![0,0],![0,1]] = ((124999996459 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (38 : Fin 88)
      ![![0,0],![1,0]] = ((124999996459 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (38 : Fin 88)
      ![![0,1],![0,0]] = ((125000003541 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (38 : Fin 88)
      ![![1,0],![0,0]] = ((125000003541 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 2) (38 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 2) (38 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_39_1 :
    (1148075352856680607703896742903 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (26 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (26 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (26 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (26 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 1 ⟨(39 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 1 ⟨(39 : Fin 88), complement (htotal3 4 (39 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (39 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (39 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (39 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (39 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (39 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (39 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 4 (39 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 4 (39 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 4 (39 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 77683416723977987327905028728105690628306028000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1937616674759950275175976216225072618743387944000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 77683416723977987327905028728105690628306028000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 1 ⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 2092983508207906249831786273681284000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((37116115067 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((462883884933 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((37116115067 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (39 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1046491748960495844793378371862944000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 260206890479458247182044629193948000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 260206890479458247182044629193948000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 1 ⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 520413780958916494364089258387896000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (39 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 260206853500211473531660110305664000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 4767105639331592019483445355292000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 1 ⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 4767105639331592019483445355292000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (39 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2383640077204276904243440301412000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(39 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 292113655206940362289954518597978000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 292113655206940362289954518597978000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 1 ⟨(39 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 584227310413880724579909037195956000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(39 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (39 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 292113706797375505336996555192464000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(39 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 135304631281845403531644257502667085825498520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7823429822056182031114175455753809828349002960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 135304631281845403531644257502667085825498520000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 1 ⟨(39 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 8094039084619872838177463970759144000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(39 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((3343315491 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((96656684509 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((3343315491 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (39 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4047019542309936419088731985379572000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 292113655206940362289954518597978000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 292113655206940362289954518597978000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 1 ⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 584227310413880724579909037195956000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (39 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 292113603616505219242912482003492000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(39 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4767105639331592019483445355292000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 4 1 ⟨(39 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 4767105639331592019483445355292000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(39 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 4 (39 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2383465562127315115240005053880000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(39 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 260206890479458247182044629193948000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 260206890479458247182044629193948000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 4 1 ⟨(39 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 520413780958916494364089258387896000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(39 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 4 (39 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 260206927458705020832429148082232000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 97662063924141382695294994976647430653325136000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1897659380359623484441196283727989138693349728000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 97662063924141382695294994976647430653325136000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 4 1 ⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 2092983508207906249831786273681284000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((11665412501 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((113334587499 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((11665412501 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 4 (39 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1046491759247410405038407901818340000000000000000000000000 := by decide +kernel
  have hn : n3 4 (39 : Fin 88) = 7249411247529971479884000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![0,0],![2,2]] = ((32878057 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![0,1],![1,2]] = ((38094171747 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![0,1],![2,1]] = ((38094171747 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![0,2],![0,2]] = ((656019008209958993711122898088643 : ℚ)/1000000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![0,2],![1,1]] = ((10056923788834558685427377101911357 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![0,2],![2,0]] = ((656019008209958993711122898088643 : ℚ)/1000000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![1,0],![1,2]] = ((38094171747 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![1,0],![2,1]] = ((38094171747 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![1,1],![0,2]] = ((10056923782062001647625877101911357 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![1,1],![1,1]] = ((190971571479393480673235622898088643 : ℚ)/250000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq10 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![1,1],![2,0]] = ((10056923782062001647625877101911357 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq11 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![1,2],![0,1]] = ((76188319059 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq12 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![1,2],![1,0]] = ((76188319059 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq13 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![2,0],![0,2]] = ((656019008209958993711122898088643 : ℚ)/1000000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq14 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![2,0],![1,1]] = ((10056923788834558685427377101911357 : ℚ)/500000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq15 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![2,0],![2,0]] = ((656019008209958993711122898088643 : ℚ)/1000000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq16 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![2,1],![0,1]] = ((76188319059 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq17 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![2,1],![1,0]] = ((76188319059 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq18 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88)
      ![![2,2],![0,0]] = ((328804643 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 1) (39 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 1) (39 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_39_2 :
    (1885687798056238305058867862051 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 2 ⟨(39 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 2 ⟨(39 : Fin 88), complement (htotal3 4 (39 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (39 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (39 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (39 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (39 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (39 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (39 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 4 (39 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 4 (39 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc8 : complement (htotal3 4 (39 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 77683416723977987327905028728105690628306028000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1937616674759950275175976216225072618743387944000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 77683416723977987327905028728105690628306028000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 2 ⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 2092983508207906249831786273681284000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((37116115067 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((462883884933 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((37116115067 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (39 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1046491748960495844793378371862944000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 260206890479458247182044629193948000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 260206890479458247182044629193948000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 2 ⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 520413780958916494364089258387896000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (39 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 260206853500211473531660110305664000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4767105639331592019483445355292000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 2 ⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 4767105639331592019483445355292000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (39 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2383640077204276904243440301412000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(39 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 584227310413880724579909037195956000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 2 ⟨(39 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 584227310413880724579909037195956000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(39 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (39 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 292113706797375505336996555192464000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(39 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 4047019542309936419088731985379572000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 4047019542309936419088731985379572000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 2 ⟨(39 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 8094039084619872838177463970759144000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(39 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (39 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4047019542309936419088731985379572000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 584227310413880724579909037195956000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 2 ⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 584227310413880724579909037195956000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (39 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 292113603616505219242912482003492000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(39 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 201142422904436242308822867082995816200376000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 4364820793522719534865799621126008367599248000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 201142422904436242308822867082995816200376000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 4 2 ⟨(39 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 4767105639331592019483445355292000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(39 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((21096912689 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((228903087311 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((21096912689 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 4 (39 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2383465562127315115240005053880000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(39 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 260206890479458247182044629193948000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 260206890479458247182044629193948000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 4 2 ⟨(39 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 520413780958916494364089258387896000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(39 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 4 (39 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 260206927458705020832429148082232000000000000000000000000 := by decide +kernel
  have hv8 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 2092983508207906249831786273681284000000000000000000000000 else 0 := by decide +kernel
  have ht8 : ∑ v, mu3 4 2 ⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 2092983508207906249831786273681284000000000000000000000000 := by decide +kernel
  have hf8 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht8, hv8 v]
    split_ifs <;> norm_num
  have hm8 : m3 4 (39 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1046491759247410405038407901818340000000000000000000000000 := by decide +kernel
  have hn : n3 4 (39 : Fin 88) = 7249411247529971479884000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![0,0],![0,2]] = ((5371785668711258368599 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![0,0],![1,1]] = ((87117725351788741631401 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![0,0],![2,0]] = ((5371785668711258368599 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![0,1],![0,1]] = ((630041967177 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq4 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![0,1],![1,0]] = ((630041967177 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq5 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![0,2],![0,0]] = ((1342946150077883190983 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq6 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![1,0],![0,1]] = ((630041967177 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq7 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![1,0],![1,0]] = ((630041967177 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq8 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![1,1],![0,0]] = ((21779430197672116809017 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  have hq9 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88)
      ![![2,0],![0,0]] = ((1342946150077883190983 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 2) (39 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 2) (39 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_40_1 :
    (1644726513686241989633564636580 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 1 ⟨(40 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 1 ⟨(40 : Fin 88), complement (htotal3 4 (40 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (40 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (40 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (40 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (40 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (40 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (40 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 362502642586818149794880345987892000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 362502642586818149794880345987892000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 1 ⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 725005285173636299589760691975784000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (40 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 362502642833087114018922031153530000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(40 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 29124471142284938606487338086014000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 1 ⟨(40 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 29124471142284938606487338086014000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(40 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (40 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14562237401603804228998883572476000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(40 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 8447249816449548166520718860230562069838000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1315340443504123889309418928500481538875860324000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 8447249816449548166520718860230562069838000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 1 ⟨(40 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1315357338003756788405751969938202000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(40 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((6422019 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((499993577981 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((6422019 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (40 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 657678678452191210413685693447134000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 657678669001878394202875984969101000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 657678669001878394202875984969101000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 1 ⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 1315357338003756788405751969938202000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (40 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 657678659551565577992066276491068000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(40 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 14562235571142469303243669043007000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 14562235571142469303243669043007000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 1 ⟨(40 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 29124471142284938606487338086014000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(40 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (40 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14562233740681134377488454513538000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 38554665813828970218193812556861829606673672000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 647895953545978359153373066862060340786652656000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 38554665813828970218193812556861829606673672000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 1 ⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 725005285173636299589760691975784000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((53178461733 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((446821538267 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((53178461733 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (40 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 362502642340549185570838660822254000000000000000000000000 := by decide +kernel
  have hn : n3 4 (40 : Fin 88) = 2069487094319678026602000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![0,1],![2,2]] = ((7036639069 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![0,2],![1,2]] = ((36394805436693321069 : ℚ)/7812500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![0,2],![2,1]] = ((36394805436693321069 : ℚ)/7812500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![1,0],![2,2]] = ((7036639069 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![1,1],![1,2]] = ((926424265840650428931 : ℚ)/3906250000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![1,1],![2,1]] = ((926424265840650428931 : ℚ)/3906250000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![1,2],![0,2]] = ((9317070204391311786591 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![1,2],![1,1]] = ((237164607595108688213409 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![1,2],![2,0]] = ((9317070204391311786591 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![2,0],![1,2]] = ((36394805436693321069 : ℚ)/7812500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![2,0],![2,1]] = ((36394805436693321069 : ℚ)/7812500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![2,1],![0,2]] = ((9317070204391311786591 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![2,1],![1,1]] = ((237164607595108688213409 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![2,1],![2,0]] = ((9317070204391311786591 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![2,2],![0,1]] = ((3518320419 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88)
      ![![2,2],![1,0]] = ((3518320419 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 1) (40 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 1) (40 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_40_2 :
    (1386294361119890561044060000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (40 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 2 ⟨(40 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 2 ⟨(40 : Fin 88), complement (htotal3 4 (40 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (40 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![2,2,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (40 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (40 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (40 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (40 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (40 : Fin 88)) (⟨![2,2,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 362502642586818149794880345987892000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 362502642586818149794880345987892000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 2 ⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 725005285173636299589760691975784000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (40 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 362502642833087114018922031153530000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(40 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 29124471142284938606487338086014000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 2 ⟨(40 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 29124471142284938606487338086014000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(40 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (40 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14562237401603804228998883572476000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(40 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 657678669001878394202875984969101000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 657678669001878394202875984969101000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 2 ⟨(40 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1315357338003756788405751969938202000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(40 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (40 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 657678678452191210413685693447134000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1315357338003756788405751969938202000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 2 ⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 1315357338003756788405751969938202000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (40 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 657678659551565577992066276491068000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(40 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 14562235571142469303243669043007000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 14562235571142469303243669043007000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 2 ⟨(40 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 29124471142284938606487338086014000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(40 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (40 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14562233740681134377488454513538000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 725005285173636299589760691975784000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 2 ⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = 725005285173636299589760691975784000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (40 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 362502642340549185570838660822254000000000000000000000000 := by decide +kernel
  have hn : n3 4 (40 : Fin 88) = 2069487094319678026602000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (40 : Fin 88)
      ![![0,0],![0,1]] = ((499999996199 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (40 : Fin 88)
      ![![0,0],![1,0]] = ((499999996199 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (40 : Fin 88)
      ![![0,1],![0,0]] = ((500000003801 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (40 : Fin 88)
      ![![1,0],![0,0]] = ((500000003801 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 2) (40 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 2) (40 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_41_1 :
    (1685836472050263068406938442272 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 1 ⟨(41 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 1 ⟨(41 : Fin 88), complement (htotal3 4 (41 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (41 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (41 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (41 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (41 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (41 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (41 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 7299305681152707765666811167097491286612056000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 191588142038411085550343626485969017426775888000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 7299305681152707765666811167097491286612056000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 1 ⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 206186753400716501081677248820164000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((17700714427 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((232299285573 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((17700714427 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (41 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 103093390073032994137022471768778000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 185818372228597189909148723228463000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 185818372228597189909148723228463000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 1 ⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 371636744457194379818297446456926000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (41 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 185818318565258696324471367151248000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 8388791445796985458025304722910000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 1 ⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 8388791445796985458025304722910000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (41 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 4194422336057108683394223215118000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(41 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 4194395722898492729012652361455000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 4194395722898492729012652361455000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 1 ⟨(41 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 8388791445796985458025304722910000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(41 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (41 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4194369109739876774631081507792000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(41 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 6723191589687792258131030898056085422932680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 358190361277818795302035384660813829154134640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6723191589687792258131030898056085422932680000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 1 ⟨(41 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 371636744457194379818297446456926000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(41 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((904538059 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((24095461941 : ℚ)/25000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((904538059 : ℚ)/50000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (41 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 185818425891935683493826079305678000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 1 ⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 103093376700358250540838624410082000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 103093376700358250540838624410082000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 1 ⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 206186753400716501081677248820164000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 1) ⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (41 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 103093363327683506944654777051386000000000000000000000000 := by decide +kernel
  have hn : n3 4 (41 : Fin 88) = 586212289303707866358000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![0,1],![2,2]] = ((894379303 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![0,2],![1,2]] = ((5980128877859689478347 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![0,2],![2,1]] = ((5980128877859689478347 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![1,0],![2,2]] = ((894379303 : ℚ)/250000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![1,1],![1,2]] = ((117231129755140310521653 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![1,1],![2,1]] = ((117231129755140310521653 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![1,2],![0,2]] = ((5980126414208789140749 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![1,2],![1,1]] = ((117231075041541210859251 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![1,2],![2,0]] = ((5980126414208789140749 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![2,0],![1,2]] = ((5980128877859689478347 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![2,0],![2,1]] = ((5980128877859689478347 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![2,1],![0,2]] = ((5980126414208789140749 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![2,1],![1,1]] = ((117231075041541210859251 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![2,1],![2,0]] = ((5980126414208789140749 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![2,2],![0,1]] = ((7155125221 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88)
      ![![2,2],![1,0]] = ((7155125221 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 1) (41 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 1) (41 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_4_41_2 :
    (1897620902154107271770348135832 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 4 2 ⟨(41 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 4 2 ⟨(41 : Fin 88), complement (htotal3 4 (41 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 4 (41 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 4 (41 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 4 (41 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 4 (41 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 4 (41 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 4 (41 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 7299305681152707765666811167097491286612056000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 191588142038411085550343626485969017426775888000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 7299305681152707765666811167097491286612056000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 4 2 ⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 206186753400716501081677248820164000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((17700714427 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((232299285573 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((17700714427 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 4 (41 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 103093390073032994137022471768778000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 185818372228597189909148723228463000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 185818372228597189909148723228463000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 4 2 ⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 371636744457194379818297446456926000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 4 (41 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 185818318565258696324471367151248000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 8388791445796985458025304722910000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 4 2 ⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 8388791445796985458025304722910000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 4 (41 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 4194422336057108683394223215118000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(41 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 8388791445796985458025304722910000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 4 2 ⟨(41 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 8388791445796985458025304722910000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(41 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 4 (41 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4194369109739876774631081507792000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(41 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 185818372228597189909148723228463000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 185818372228597189909148723228463000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 4 2 ⟨(41 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 371636744457194379818297446456926000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(41 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 4 (41 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 185818425891935683493826079305678000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 4 2 ⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 206186753400716501081677248820164000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 4 2 ⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 206186753400716501081677248820164000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 4 2) ⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 4 (41 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 103093363327683506944654777051386000000000000000000000000 := by decide +kernel
  have hn : n3 4 (41 : Fin 88) = 586212289303707866358000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![0,0],![0,2]] = ((3112910146851023931709 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![0,0],![1,1]] = ((42641754000148976068291 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![0,0],![2,0]] = ((3112910146851023931709 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![0,1],![0,1]] = ((633962731997 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![0,1],![1,0]] = ((633962731997 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![0,2],![0,0]] = ((3112910954428418949157 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![1,0],![0,1]] = ((633962731997 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![1,0],![1,0]] = ((633962731997 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![1,1],![0,0]] = ((42641741899321581050843 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88)
      ![![2,0],![0,0]] = ((3112910954428418949157 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 4) (n3 4) (m3 4)
      (mu3 4 2) (41 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 4) (n3 4) (m3 4)
        (mu3 4 2) (41 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1386294361119889816358880000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (38 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1148075352856680607703896742903 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (39 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (26 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (26 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (26 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (26 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1885687798056238305058867862051 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (39 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1644726513686241989633564636580 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (40 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119890561044060000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (40 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1685836472050263068406938442272 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 1) (41 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1897620902154107271770348135832 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 4) (n3 4) (m3 4) (mu3 4 2) (41 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_4_38_2, L3C.mx_4_39_1, L3C.mx_4_39_2, L3C.mx_4_40_1, L3C.mx_4_40_2, L3C.mx_4_41_1, L3C.mx_4_41_2⟩
