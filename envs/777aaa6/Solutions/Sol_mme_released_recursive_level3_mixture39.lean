-- Prove2me | solution 1 for mme_released_recursive_level3_mixture39
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T15:53:16.301187+00:00
-- url     : https://prove2.me/submissions/33efdedc-da95-49ac-97d1-5d8758dcd69a

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

theorem mx_1_45_2 :
    (1386294316191790063424089995593 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (45 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 2 ⟨(45 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 2 ⟨(45 : Fin 88), complement (htotal3 1 (45 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(45 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42177999473752421346594303219530000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42177999473752421346594303219530000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 2 ⟨(45 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84355998947504842693188606439060000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(45 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (45 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42201699844807346135577767996180000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(45 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25832258368801458726811393560940000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 2 ⟨(45 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25832258368801458726811393560940000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(45 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (45 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12923697809027521589201461965840000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(45 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12916129184400729363405696780470000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12916129184400729363405696780470000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 2 ⟨(45 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25832258368801458726811393560940000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(45 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (45 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12908560559773937137609931595100000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(45 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84355998947504842693188606439060000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 2 ⟨(45 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84355998947504842693188606439060000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(45 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (45 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42154299102697496557610838442880000000000000000000000000 := by decide +kernel
  have hn : n3 1 (45 : Fin 88) = 110188257316306301420000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (45 : Fin 88)
      ![![0,0],![0,1]] = ((124963399579 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (45 : Fin 88)
      ![![0,0],![1,0]] = ((124963399579 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (45 : Fin 88)
      ![![0,1],![0,0]] = ((125036600421 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (45 : Fin 88)
      ![![1,0],![0,0]] = ((125036600421 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 2) (45 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 2) (45 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_46_1 :
    (1685944165777459626983582808876 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 1 ⟨(46 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 1 ⟨(46 : Fin 88), complement (htotal3 1 (46 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (46 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (46 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (46 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (46 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (46 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (46 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 6477038608522815387402503159860620383295360000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 170064094670786556258507177841754759233409280000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6477038608522815387402503159860620383295360000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 1 ⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 183018171887832187033312184161476000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((221188371 : ℚ)/6250000000) else if 3 * (v 0).val + (v 1).val = 4 then ((2903811629 : ℚ)/3125000000) else if 3 * (v 0).val + (v 1).val = 6 then ((221188371 : ℚ)/6250000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (46 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 91509086336924622790262153306168000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(46 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 165021834185423244290061545171587000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 165021834185423244290061545171587000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 1 ⟨(46 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 330043668370846488580123090343174000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(46 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (46 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 165021865582119863365805102578770000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(46 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 7479258116958491572564725495350000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 1 ⟨(46 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 7479258116958491572564725495350000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(46 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (46 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3739651921945639190205838474760000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(46 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 3739629058479245786282362747675000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3739629058479245786282362747675000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 1 ⟨(46 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 7479258116958491572564725495350000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(46 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (46 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3739606195012852382358887020590000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(46 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 5964986854947787035532192270155391140650272000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 318113694660950914509058705802863217718699456000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 5964986854947787035532192270155391140650272000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 1 ⟨(46 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 330043668370846488580123090343174000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(46 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((1129582883 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((30120417117 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1129582883 : ℚ)/62500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (46 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 165021802788726625214317987764404000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(46 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 91509085943916093516656092080738000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 91509085943916093516656092080738000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 1 ⟨(46 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 183018171887832187033312184161476000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(46 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (46 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 91509085550907564243050030855308000000000000000000000000 := by decide +kernel
  have hn : n3 1 (46 : Fin 88) = 520541098375637167186000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![0,1],![2,2]] = ((1436814963 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![0,2],![1,2]] = ((373470281550176244371 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![0,2],![2,1]] = ((373470281550176244371 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![1,0],![2,2]] = ((1436814963 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![1,1],![1,2]] = ((7326776932543573755629 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![1,1],![2,1]] = ((7326776932543573755629 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![1,2],![0,2]] = ((149388139204624169163 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![1,2],![1,1]] = ((2930711490939125830837 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![1,2],![2,0]] = ((149388139204624169163 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![2,0],![1,2]] = ((373470281550176244371 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![2,0],![2,1]] = ((373470281550176244371 : ℚ)/62500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![2,1],![0,2]] = ((149388139204624169163 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![2,1],![1,1]] = ((2930711490939125830837 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![2,1],![2,0]] = ((149388139204624169163 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![2,2],![0,1]] = ((359208133 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88)
      ![![2,2],![1,0]] = ((359208133 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 1) (46 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 1) (46 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_46_2 :
    (1897568620864198708016396621391 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 2 ⟨(46 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 2 ⟨(46 : Fin 88), complement (htotal3 1 (46 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (46 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (46 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (46 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (46 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (46 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (46 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 6477038608522815387402503159860620383295360000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 170064094670786556258507177841754759233409280000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6477038608522815387402503159860620383295360000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 2 ⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 183018171887832187033312184161476000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((221188371 : ℚ)/6250000000) else if 3 * (v 0).val + (v 1).val = 4 then ((2903811629 : ℚ)/3125000000) else if 3 * (v 0).val + (v 1).val = 6 then ((221188371 : ℚ)/6250000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (46 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 91509086336924622790262153306168000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(46 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 165021834185423244290061545171587000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 165021834185423244290061545171587000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 2 ⟨(46 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 330043668370846488580123090343174000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(46 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (46 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 165021865582119863365805102578770000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(46 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 7479258116958491572564725495350000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 2 ⟨(46 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 7479258116958491572564725495350000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(46 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (46 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3739651921945639190205838474760000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(46 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 7479258116958491572564725495350000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 2 ⟨(46 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 7479258116958491572564725495350000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(46 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (46 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3739606195012852382358887020590000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(46 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 165021834185423244290061545171587000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 165021834185423244290061545171587000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 2 ⟨(46 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 330043668370846488580123090343174000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(46 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (46 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 165021802788726625214317987764404000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(46 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 183018171887832187033312184161476000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 2 ⟨(46 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 183018171887832187033312184161476000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(46 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (46 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 91509085550907564243050030855308000000000000000000000000 := by decide +kernel
  have hn : n3 1 (46 : Fin 88) = 520541098375637167186000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![0,0],![0,2]] = ((19442024489388720369 : ℚ)/3125000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![0,0],![1,1]] = ((266464607601236279631 : ℚ)/1562500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![0,0],![2,0]] = ((19442024489388720369 : ℚ)/3125000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![0,1],![0,1]] = ((634039597259 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![0,1],![1,0]] = ((634039597259 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![0,2],![0,0]] = ((9721012328192970237 : ℚ)/1562500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![1,0],![0,1]] = ((634039597259 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![1,0],![1,0]] = ((634039597259 : ℚ)/4000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![1,1],![0,0]] = ((133232236267900779763 : ℚ)/781250000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88)
      ![![2,0],![0,0]] = ((9721012328192970237 : ℚ)/1562500000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 2) (46 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 2) (46 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_47_1 :
    (1859734025245591189435352675657 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 1 ⟨(47 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 1 ⟨(47 : Fin 88), complement (htotal3 1 (47 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (47 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (47 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (47 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (47 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (47 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (47 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 1 (47 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 1 (47 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 6747619630057753587546021745212000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 1 ⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 6747619630057753587546021745212000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (47 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3374002508600590728849442027674000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 692588648016122468238703924336575000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 692588648016122468238703924336575000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 1 ⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1385177296032244936477407848673150000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (47 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 692587403125525253991102682303026000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 413233297932591279155664636454312573280677056000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7738704456725451764609614426404350853438645888000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 413233297932591279155664636454312573280677056000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 1 ⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 8565171052590634322920943699312976000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((12061443239 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((112938556761 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((12061443239 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (47 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4282586629281577904328638690498712000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 130519035545158294630051215134331000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 130519035545158294630051215134331000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 1 ⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 261038071090316589260102430268662000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (47 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 130517516369189062291493528011404000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 261038071090316589260102430268662000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 1 ⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 261038071090316589260102430268662000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (47 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 130520554721127526968608902257258000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(47 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 4282585526295317161460471849656488000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 4282585526295317161460471849656488000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 1 ⟨(47 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 8565171052590634322920943699312976000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(47 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (47 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4282584423309056418592305008814264000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(47 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 29078372098408786306870379860699781501508750000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1327020551835427363863667088951750436996982500000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 29078372098408786306870379860699781501508750000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 1 1 ⟨(47 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1385177296032244936477407848673150000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(47 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((839701089 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((19160298911 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((839701089 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 1 (47 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 692589892906719682486305166370124000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(47 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 3373809815028876793773010872606000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 3373809815028876793773010872606000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 1 1 ⟨(47 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 6747619630057753587546021745212000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(47 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 1 (47 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3373617121457162858696579717538000000000000000000000000 := by decide +kernel
  have hn : n3 1 (47 : Fin 88) = 10218134039343253602246000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![0,0],![1,2]] = ((6551810571 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![0,0],![2,1]] = ((6551810571 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![0,1],![0,2]] = ((21643458073279476406379 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![0,1],![1,1]] = ((221804700234220523593621 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![0,1],![2,0]] = ((21643458073279476406379 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![0,2],![0,1]] = ((10821736802032534778241 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![0,2],![1,0]] = ((10821736802032534778241 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![1,0],![0,2]] = ((21643458073279476406379 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![1,0],![1,1]] = ((221804700234220523593621 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![1,0],![2,0]] = ((21643458073279476406379 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![1,1],![0,1]] = ((110902457239467465221759 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![1,1],![1,0]] = ((110902457239467465221759 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![1,2],![0,0]] = ((13103286077 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![2,0],![0,1]] = ((10821736802032534778241 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![2,0],![1,0]] = ((10821736802032534778241 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88)
      ![![2,1],![0,0]] = ((13103286077 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 1) (47 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 1) (47 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_47_2 :
    (1167061976134324951841428000817 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 2 ⟨(47 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 2 ⟨(47 : Fin 88), complement (htotal3 1 (47 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (47 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (47 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (47 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (47 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (47 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (47 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 1 (47 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 1 (47 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 6747619630057753587546021745212000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 2 ⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 6747619630057753587546021745212000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (47 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3374002508600590728849442027674000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 692588648016122468238703924336575000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 692588648016122468238703924336575000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 2 ⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1385177296032244936477407848673150000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (47 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 692587403125525253991102682303026000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 413233297932591279155664636454312573280677056000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7738704456725451764609614426404350853438645888000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 413233297932591279155664636454312573280677056000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 2 ⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 8565171052590634322920943699312976000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((12061443239 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((112938556761 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((12061443239 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (47 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4282586629281577904328638690498712000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 130519035545158294630051215134331000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 130519035545158294630051215134331000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 2 ⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 261038071090316589260102430268662000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (47 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 130517516369189062291493528011404000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 130519035545158294630051215134331000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 130519035545158294630051215134331000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 2 ⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 261038071090316589260102430268662000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (47 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 130520554721127526968608902257258000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(47 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 8519829657980561597549503037177585094826656000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8548131393274673199725844693238620829810346688000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 8519829657980561597549503037177585094826656000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 2 ⟨(47 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 8565171052590634322920943699312976000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(47 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((497353153 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((249502646847 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((497353153 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (47 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4282584423309056418592305008814264000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(47 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 692588648016122468238703924336575000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 692588648016122468238703924336575000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 1 2 ⟨(47 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1385177296032244936477407848673150000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(47 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 1 (47 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 692589892906719682486305166370124000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(47 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 6747619630057753587546021745212000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 1 2 ⟨(47 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 6747619630057753587546021745212000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(47 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 1 (47 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3373617121457162858696579717538000000000000000000000000 := by decide +kernel
  have hn : n3 1 (47 : Fin 88) = 10218134039343253602246000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![0,0],![2,2]] = ((330159803 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![0,1],![1,2]] = ((20138398217 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![0,1],![2,1]] = ((20138398217 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![0,2],![0,2]] = ((628548234871058682178224654769 : ℚ)/15625000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![0,2],![1,1]] = ((160601824695604590584509275345231 : ℚ)/7812500000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![0,2],![2,0]] = ((628548234871058682178224654769 : ℚ)/15625000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![1,0],![1,2]] = ((20138398217 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![1,0],![2,1]] = ((20138398217 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![1,1],![0,2]] = ((160601745000774302028259275345231 : ℚ)/7812500000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![1,1],![1,1]] = ((2952513207287500048705053224654769 : ℚ)/3906250000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![1,1],![2,0]] = ((160601745000774302028259275345231 : ℚ)/7812500000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![1,2],![0,1]] = ((40276823277 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![1,2],![1,0]] = ((40276823277 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![2,0],![0,2]] = ((628548234871058682178224654769 : ℚ)/15625000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![2,0],![1,1]] = ((160601824695604590584509275345231 : ℚ)/7812500000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![2,0],![2,0]] = ((628548234871058682178224654769 : ℚ)/15625000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq16 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![2,1],![0,1]] = ((40276823277 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq17 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![2,1],![1,0]] = ((40276823277 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq18 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88)
      ![![2,2],![0,0]] = ((330197519 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 2) (47 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 2) (47 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_48_1 :
    (1945700194340168550320449002362 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 1 ⟨(48 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 1 ⟨(48 : Fin 88), complement (htotal3 1 (48 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (48 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (48 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (48 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (48 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (48 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (48 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 47292893809349512075135198326390000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 1 ⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 47292893809349512075135198326390000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (48 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23646422311264392377154732957682000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1011849281078144124409826471671320000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1011849281078144124409826471671320000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 1 ⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2023698562156288248819652943342640000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (48 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1011849297536848079217460416441300000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 64558694508378690862743392428546406755164960000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1008215512679911669225725073473877186489670080000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 64558694508378690862743392428546406755164960000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 1 ⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 1137332901696669050951211858330970000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((3547702173 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((27702297827 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((3547702173 : ℚ)/62500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 568666442883669307578929268757790000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1137332901696669050951211858330970000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 1 ⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1137332901696669050951211858330970000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (48 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 568666458812999743372282589573180000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(48 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1011849281078144124409826471671320000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1011849281078144124409826471671320000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 1 ⟨(48 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2023698562156288248819652943342640000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(48 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1011849264619440169602192526901340000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 1 ⟨(48 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 996351696914339496596300047638193384078380000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 45300190415520833081942598231113613231843240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 996351696914339496596300047638193384078380000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 1 ⟨(48 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 47292893809349512075135198326390000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 1) ⟨(48 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((10533841521 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((239466158479 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10533841521 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23646471498085119697980465368708000000000000000000000000 := by decide +kernel
  have hn : n3 1 (48 : Fin 88) = 3208324357662306811846000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![0,0],![0,2]] = ((5108199699063985788627 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![0,0],![1,1]] = ((41046179900186014211373 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![0,0],![2,0]] = ((5108199699063985788627 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![0,1],![0,1]] = ((15769123821 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![0,1],![1,0]] = ((15769123821 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![0,2],![0,0]] = ((2554099859821789917759 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![1,0],![0,1]] = ((15769123821 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![1,0],![1,0]] = ((15769123821 : ℚ)/100000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![1,1],![0,0]] = ((20523091235553210082241 : ℚ)/125000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88)
      ![![2,0],![0,0]] = ((2554099859821789917759 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 1) (48 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 1) (48 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_1_48_2 :
    (1659095089113328567582567249624 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 1 2 ⟨(48 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 1 2 ⟨(48 : Fin 88), complement (htotal3 1 (48 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 1 (48 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 1 (48 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 1 (48 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 1 (48 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 1 (48 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 1 (48 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 47292893809349512075135198326390000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 1 2 ⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 47292893809349512075135198326390000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 1 (48 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23646422311264392377154732957682000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1011849281078144124409826471671320000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1011849281078144124409826471671320000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 1 2 ⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 2023698562156288248819652943342640000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 1 (48 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1011849297536848079217460416441300000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 64558694508378690862743392428546406755164960000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1008215512679911669225725073473877186489670080000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 64558694508378690862743392428546406755164960000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 1 2 ⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 1137332901696669050951211858330970000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((3547702173 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((27702297827 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 6 then ((3547702173 : ℚ)/62500000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 1 (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 568666442883669307578929268757790000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 568666450848334525475605929165485000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 568666450848334525475605929165485000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 1 2 ⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1137332901696669050951211858330970000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 1 (48 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 568666458812999743372282589573180000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(48 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 2023698562156288248819652943342640000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 1 2 ⟨(48 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 2023698562156288248819652943342640000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(48 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 1 (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1011849264619440169602192526901340000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 1 2 ⟨(48 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 23646446904674756037567599163195000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 23646446904674756037567599163195000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 1 2 ⟨(48 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 47292893809349512075135198326390000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 1 2) ⟨(48 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 1 (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23646471498085119697980465368708000000000000000000000000 := by decide +kernel
  have hn : n3 1 (48 : Fin 88) = 3208324357662306811846000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![0,1],![2,2]] = ((3685174699 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![0,2],![1,2]] = ((125764040678266252029 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![0,2],![2,1]] = ((125764040678266252029 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![1,0],![2,2]] = ((3685174699 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![1,1],![1,2]] = ((2953171275915483747971 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![1,1],![2,1]] = ((2953171275915483747971 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![1,2],![0,2]] = ((62882022100567254909 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![1,2],![1,1]] = ((1476585683774432745091 : ℚ)/6250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![1,2],![2,0]] = ((62882022100567254909 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![2,0],![1,2]] = ((125764040678266252029 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![2,0],![2,1]] = ((125764040678266252029 : ℚ)/25000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![2,1],![0,2]] = ((62882022100567254909 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![2,1],![1,1]] = ((1476585683774432745091 : ℚ)/6250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![2,1],![2,0]] = ((62882022100567254909 : ℚ)/12500000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![2,2],![0,1]] = ((7370334067 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88)
      ![![2,2],![1,0]] = ((7370334067 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 1) (n3 1) (m3 1)
      (mu3 1 2) (48 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 1) (n3 1) (m3 1)
        (mu3 1 2) (48 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1386294316191790063424089995593 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (45 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1685944165777459626983582808876 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (46 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1897568620864198708016396621391 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (46 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1859734025245591189435352675657 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (47 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1167061976134324951841428000817 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (47 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1945700194340168550320449002362 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 1) (48 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1659095089113328567582567249624 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 1) (n3 1) (m3 1) (mu3 1 2) (48 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_1_45_2, L3C.mx_1_46_1, L3C.mx_1_46_2, L3C.mx_1_47_1, L3C.mx_1_47_2, L3C.mx_1_48_1, L3C.mx_1_48_2⟩
