-- Prove2me | solution 1 for mme_released_recursive_level3_mixture22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T13:24:01.096473+00:00
-- url     : https://prove2.me/submissions/b303ee19-88f5-495e-93bc-c78c025485b5

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

theorem mx_0_77_1 :
    (1859688689610567111003463819947 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(77 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(77 : Fin 88), complement (htotal3 0 (77 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![1,2]] + g ![![0,0],![2,1]] + g ![![0,1],![0,2]] + g ![![0,1],![1,1]] + g ![![0,1],![2,0]] + g ![![0,2],![0,1]] + g ![![0,2],![1,0]] + g ![![1,0],![0,2]] + g ![![1,0],![1,1]] + g ![![1,0],![2,0]] + g ![![1,1],![0,1]] + g ![![1,1],![1,0]] + g ![![1,2],![0,0]] + g ![![2,0],![0,1]] + g ![![2,0],![1,0]] + g ![![2,1],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (77 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (77 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (77 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (77 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (77 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (77 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (77 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (77 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 7098179432574057430564115055657000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 7098179432574057430564115055657000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (77 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3549084569013167800345364116662000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 729257115001535224106820642603072000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 729257115001535224106820642603072000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1458514230003070448213641285206144000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (77 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 729257282511145594362607873112340000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 435029631422364479219394239936689296109790790000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8146768725900518601928369220867976407780418420000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 435029631422364479219394239936689296109790790000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 9016827988745247560367157700741355000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((24123207849 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((225876792151 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((24123207849 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4508413832548142428723076975071026000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 137331379713040584978818449498422000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 137331379713040584978818449498422000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 274662759426081169957636898996844000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (77 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 137331594769046911857427382990670000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 274662759426081169957636898996844000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 1 ⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 274662759426081169957636898996844000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (77 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 137331164657034258100209516006174000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(77 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 4508413994372623780183578850370677500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 4508413994372623780183578850370677500000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 1 ⟨(77 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 9016827988745247560367157700741355000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(77 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4508414156197105131644080725670329000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(77 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 30618780769835713072575583156774360688860800000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1397276668463399022068490118892595278622278400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 30618780769835713072575583156774360688860800000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 1 ⟨(77 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1458514230003070448213641285206144000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(77 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((839725253 : ℚ)/40000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((19160274747 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((839725253 : ℚ)/40000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 729256947491924853851033412093804000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(77 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 3549089716287028715282057527828500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 3549089716287028715282057527828500000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 1 ⟨(77 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 7098179432574057430564115055657000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(77 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (77 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3549094863560889630218750938995000000000000000000000000 := by decide +kernel
  have hn : n3 0 (77 : Fin 88) = 10757103157606973235969000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![0,0],![1,2]] = ((3274121461 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![0,0],![2,1]] = ((3274121461 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![0,1],![0,2]] = ((10821882713630899686659 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![0,1],![1,1]] = ((110903998361619100313341 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![0,1],![2,0]] = ((10821882713630899686659 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![0,2],![0,1]] = ((338183801904090754403 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![0,2],![1,0]] = ((338183801904090754403 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![1,0],![0,2]] = ((10821882713630899686659 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![1,0],![1,1]] = ((110903998361619100313341 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![1,0],![2,0]] = ((10821882713630899686659 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![1,1],![0,1]] = ((3465749503330284245597 : ℚ)/15625000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![1,1],![1,0]] = ((3465749503330284245597 : ℚ)/15625000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![1,2],![0,0]] = ((2619305357 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![2,0],![0,1]] = ((338183801904090754403 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![2,0],![1,0]] = ((338183801904090754403 : ℚ)/31250000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88)
      ![![2,1],![0,0]] = ((2619305357 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (77 : Fin 88)) _ ({![![0,0],![1,2]], ![![0,0],![2,1]], ![![0,1],![0,2]], ![![0,1],![1,1]], ![![0,1],![2,0]], ![![0,2],![0,1]], ![![0,2],![1,0]], ![![1,0],![0,2]], ![![1,0],![1,1]], ![![1,0],![2,0]], ![![1,1],![0,1]], ![![1,1],![1,0]], ![![1,2],![0,0]], ![![2,0],![0,1]], ![![2,0],![1,0]], ![![2,1],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (77 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_77_2 :
    (1167102278938330709868349066786 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 2 ⟨(77 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 2 ⟨(77 : Fin 88), complement (htotal3 0 (77 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![2,2]] + g ![![0,1],![1,2]] + g ![![0,1],![2,1]] + g ![![0,2],![0,2]] + g ![![0,2],![1,1]] + g ![![0,2],![2,0]] + g ![![1,0],![1,2]] + g ![![1,0],![2,1]] + g ![![1,1],![0,2]] + g ![![1,1],![1,1]] + g ![![1,1],![2,0]] + g ![![1,2],![0,1]] + g ![![1,2],![1,0]] + g ![![2,0],![0,2]] + g ![![2,0],![1,1]] + g ![![2,0],![2,0]] + g ![![2,1],![0,1]] + g ![![2,1],![1,0]] + g ![![2,2],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (77 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (77 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (77 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (77 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (77 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (77 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hc6 : complement (htotal3 0 (77 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc7 : complement (htotal3 0 (77 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 7098179432574057430564115055657000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 2 ⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 7098179432574057430564115055657000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (77 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3549084569013167800345364116662000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 729257115001535224106820642603072000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 729257115001535224106820642603072000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 2 ⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1458514230003070448213641285206144000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (77 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 729257282511145594362607873112340000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 435029631422364479219394239936689296109790790000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8146768725900518601928369220867976407780418420000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 435029631422364479219394239936689296109790790000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 2 ⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 9016827988745247560367157700741355000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((24123207849 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((225876792151 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((24123207849 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4508413832548142428723076975071026000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 137331379713040584978818449498422000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 137331379713040584978818449498422000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 2 ⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 274662759426081169957636898996844000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (77 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 137331594769046911857427382990670000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 137331379713040584978818449498422000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 137331379713040584978818449498422000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 2 ⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 274662759426081169957636898996844000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (77 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 137331164657034258100209516006174000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(77 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 8969980968761441739214794529235576282683950000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8998888026807724676888728111682883847434632100000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 8969980968761441739214794529235576282683950000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 2 ⟨(77 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 9016827988745247560367157700741355000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(77 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((99480449 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((49900519551 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((99480449 : ℚ)/100000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4508414156197105131644080725670329000000000000000000000000 := by decide +kernel
  have hv6 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(77 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 729257115001535224106820642603072000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 729257115001535224106820642603072000000000000000000000000 else 0 := by decide +kernel
  have ht6 : ∑ v, mu3 0 2 ⟨(77 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 1458514230003070448213641285206144000000000000000000000000 := by decide +kernel
  have hf6 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(77 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht6, hv6 v]
    split_ifs <;> norm_num
  have hm6 : m3 0 (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 729256947491924853851033412093804000000000000000000000000 := by decide +kernel
  have hv7 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(77 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 7098179432574057430564115055657000000000000000000000000 else 0 := by decide +kernel
  have ht7 : ∑ v, mu3 0 2 ⟨(77 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 7098179432574057430564115055657000000000000000000000000 := by decide +kernel
  have hf7 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(77 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht7, hv7 v]
    split_ifs <;> norm_num
  have hm7 : m3 0 (77 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3549094863560889630218750938995000000000000000000000000 := by decide +kernel
  have hn : n3 0 (77 : Fin 88) = 10757103157606973235969000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![0,0],![2,2]] = ((65986071 : ℚ)/200000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![0,1],![1,2]] = ((40279828573 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![0,1],![2,1]] = ((40279828573 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![0,2],![0,2]] = ((402310384386317646945732954759 : ℚ)/10000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![0,2],![1,1]] = ((102785227792240033418964267045241 : ℚ)/5000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![0,2],![2,0]] = ((402310384386317646945732954759 : ℚ)/10000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![1,0],![1,2]] = ((40279828573 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![1,0],![2,1]] = ((40279828573 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![1,1],![0,2]] = ((102785234900536165494444267045241 : ℚ)/5000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![1,1],![1,1]] = ((1889579313910337483439645732954759 : ℚ)/2500000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq10 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![1,1],![2,0]] = ((102785234900536165494444267045241 : ℚ)/5000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq11 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![1,2],![0,1]] = ((40279824153 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq12 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![1,2],![1,0]] = ((40279824153 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq13 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![2,0],![0,2]] = ((402310384386317646945732954759 : ℚ)/10000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq14 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![2,0],![1,1]] = ((102785227792240033418964267045241 : ℚ)/5000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq15 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![2,0],![2,0]] = ((402310384386317646945732954759 : ℚ)/10000000000000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq16 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![2,1],![0,1]] = ((40279824153 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq17 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![2,1],![1,0]] = ((40279824153 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  have hq18 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88)
      ![![2,2],![0,0]] = ((164964699 : ℚ)/500000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 2) (77 : Fin 88)) _ ({![![0,0],![2,2]], ![![0,1],![1,2]], ![![0,1],![2,1]], ![![0,2],![0,2]], ![![0,2],![1,1]], ![![0,2],![2,0]], ![![1,0],![1,2]], ![![1,0],![2,1]], ![![1,1],![0,2]], ![![1,1],![1,1]], ![![1,1],![2,0]], ![![1,2],![0,1]], ![![1,2],![1,0]], ![![2,0],![0,2]], ![![2,0],![1,1]], ![![2,0],![2,0]], ![![2,1],![0,1]], ![![2,1],![1,0]], ![![2,2],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 2) (77 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_78_1 :
    (1685792663679872345099737498522 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(78 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(78 : Fin 88), complement (htotal3 0 (78 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,1],![2,2]] + g ![![0,2],![1,2]] + g ![![0,2],![2,1]] + g ![![1,0],![2,2]] + g ![![1,1],![1,2]] + g ![![1,1],![2,1]] + g ![![1,2],![0,2]] + g ![![1,2],![1,1]] + g ![![1,2],![2,0]] + g ![![2,0],![1,2]] + g ![![2,0],![2,1]] + g ![![2,1],![0,2]] + g ![![2,1],![1,1]] + g ![![2,1],![2,0]] + g ![![2,2],![0,1]] + g ![![2,2],![1,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (78 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (78 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (78 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (78 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (78 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (78 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 6812748140356397124308575581824792126979144000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 178865092052151472857266830497846415746041712000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6812748140356397124308575581824792126979144000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 192490588332864267105883981661496000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((35392629839 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((464607370161 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((35392629839 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 96245328674912340846861130004424000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 173493636200660535926078678762664000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 173493636200660535926078678762664000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 346987272401321071852157357525328000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (78 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 173493541828241202482634307513608000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 7837072649275841193958660813176000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 7837072649275841193958660813176000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (78 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3918565600240049811626126146992000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(78 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 3918536324637920596979330406588000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3918536324637920596979330406588000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(78 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 7837072649275841193958660813176000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(78 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3918507049035791382332534666184000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(78 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 6273239467425490517790817995766559623749168000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 334440793466470090816575721533794880752501664000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6273239467425490517790817995766559623749168000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 1 ⟨(78 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 346987272401321071852157357525328000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(78 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((18079163031 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((481920836969 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((18079163031 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 173493730573079869369523050011720000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(78 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 96245294166432133552941990830748000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 96245294166432133552941990830748000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 1 ⟨(78 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 192490588332864267105883981661496000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(78 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (78 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 96245259657951926259022851657072000000000000000000000000 := by decide +kernel
  have hn : n3 0 (78 : Fin 88) = 547314933383461180152000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![0,1],![2,2]] = ((7159510567 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![0,2],![1,2]] = ((5977359955229829128589 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![0,2],![2,1]] = ((5977359955229829128589 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![1,0],![2,2]] = ((7159510567 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![1,1],![1,2]] = ((117232807900270170871411 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![1,1],![2,1]] = ((117232807900270170871411 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![1,2],![0,2]] = ((11954709212705796710903 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![1,2],![1,1]] = ((234465391019794203289097 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![1,2],![2,0]] = ((11954709212705796710903 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![2,0],![1,2]] = ((5977359955229829128589 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq10 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![2,0],![2,1]] = ((5977359955229829128589 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq11 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![2,1],![0,2]] = ((11954709212705796710903 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq12 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![2,1],![1,1]] = ((234465391019794203289097 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq13 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![2,1],![2,0]] = ((11954709212705796710903 : ℚ)/2000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq14 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![2,2],![0,1]] = ((3579808773 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq15 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88)
      ![![2,2],![1,0]] = ((3579808773 : ℚ)/1000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (78 : Fin 88)) _ ({![![0,1],![2,2]], ![![0,2],![1,2]], ![![0,2],![2,1]], ![![1,0],![2,2]], ![![1,1],![1,2]], ![![1,1],![2,1]], ![![1,2],![0,2]], ![![1,2],![1,1]], ![![1,2],![2,0]], ![![2,0],![1,2]], ![![2,0],![2,1]], ![![2,1],![0,2]], ![![2,1],![1,1]], ![![2,1],![2,0]], ![![2,2],![0,1]], ![![2,2],![1,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (78 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_78_2 :
    (1897595367023868788626988830248 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 2 ⟨(78 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 2 ⟨(78 : Fin 88), complement (htotal3 0 (78 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,2]] + g ![![0,0],![1,1]] + g ![![0,0],![2,0]] + g ![![0,1],![0,1]] + g ![![0,1],![1,0]] + g ![![0,2],![0,0]] + g ![![1,0],![0,1]] + g ![![1,0],![1,0]] + g ![![1,1],![0,0]] + g ![![2,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (78 : Fin 88)) (⟨![0,2,2], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (78 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (78 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (78 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (78 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (78 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,2,2], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 6812748140356397124308575581824792126979144000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 178865092052151472857266830497846415746041712000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6812748140356397124308575581824792126979144000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 2 ⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = 192490588332864267105883981661496000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((35392629839 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((464607370161 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((35392629839 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 96245328674912340846861130004424000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 173493636200660535926078678762664000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 173493636200660535926078678762664000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 2 ⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 346987272401321071852157357525328000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (78 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 173493541828241202482634307513608000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 7837072649275841193958660813176000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 2 ⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 7837072649275841193958660813176000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (78 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3918565600240049811626126146992000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(78 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then 7837072649275841193958660813176000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 2 ⟨(78 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 7837072649275841193958660813176000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(78 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3918507049035791382332534666184000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(78 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 173493636200660535926078678762664000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 173493636200660535926078678762664000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 2 ⟨(78 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 346987272401321071852157357525328000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(78 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 173493730573079869369523050011720000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(78 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 192490588332864267105883981661496000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 2 ⟨(78 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 192490588332864267105883981661496000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(78 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (78 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 96245259657951926259022851657072000000000000000000000000 := by decide +kernel
  have hn : n3 0 (78 : Fin 88) = 547314933383461180152000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![0,0],![0,2]] = ((3111894670746861088327 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![0,0],![1,1]] = ((42640477112253138911673 : ℚ)/250000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![0,0],![2,0]] = ((3111894670746861088327 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![0,1],![0,1]] = ((316990503307 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![0,1],![1,0]] = ((316990503307 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![0,2],![0,0]] = ((6223793804539737504393 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![1,0],![0,1]] = ((316990503307 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![1,0],![1,0]] = ((316990503307 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![1,1],![0,0]] = ((85280959322460262495607 : ℚ)/500000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88)
      ![![2,0],![0,0]] = ((6223793804539737504393 : ℚ)/1000000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 2) (78 : Fin 88)) _ ({![![0,0],![0,2]], ![![0,0],![1,1]], ![![0,0],![2,0]], ![![0,1],![0,1]], ![![0,1],![1,0]], ![![0,2],![0,0]], ![![1,0],![0,1]], ![![1,0],![1,0]], ![![1,1],![0,0]], ![![2,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 2) (78 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_79_1 :
    (1810284755295356136751912948110 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(79 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(79 : Fin 88), complement (htotal3 0 (79 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,2],![2,2]] + g ![![1,1],![2,2]] + g ![![1,2],![1,2]] + g ![![1,2],![2,1]] + g ![![2,0],![2,2]] + g ![![2,1],![1,2]] + g ![![2,1],![2,1]] + g ![![2,2],![0,2]] + g ![![2,2],![1,1]] + g ![![2,2],![2,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (79 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (79 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (79 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (79 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42232242412414726408440493659450000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42232242412414726408440493659450000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84464484824829452816880987318900000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (79 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42230357244875889090198562648500000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25817136173108185803119012681100000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25817136173108185803119012681100000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (79 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12929032066834773569987456505300000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(79 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 463892317199712295002607263915904786008900000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 24889351538708761213113798153268190427982200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 463892317199712295002607263915904786008900000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(79 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25817136173108185803119012681100000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(79 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then ((17968387899 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((482031612101 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((17968387899 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12888104106273412233131556175800000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(79 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42232242412414726408440493659450000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42232242412414726408440493659450000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(79 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84464484824829452816880987318900000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(79 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (79 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42234127579953563726682424670400000000000000000000000000 := by decide +kernel
  have hn : n3 0 (79 : Fin 88) = 110281620997937638620000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![0,2],![2,2]] = ((209988257126313102591 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![1,1],![2,2]] = ((5633280997373686897409 : ℚ)/50000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![1,2],![1,2]] = ((153179621519 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![1,2],![2,1]] = ((153179621519 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq4 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![2,0],![2,2]] = ((209988257126313102591 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq5 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![2,1],![1,2]] = ((153179621519 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq6 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![2,1],![2,1]] = ((153179621519 : ℚ)/800000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq7 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![2,2],![0,2]] = ((421310207871974196237 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq8 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![2,2],![1,1]] = ((11302340523628025803763 : ℚ)/100000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq9 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88)
      ![![2,2],![2,0]] = ((421310207871974196237 : ℚ)/200000000000000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (79 : Fin 88)) _ ({![![0,2],![2,2]], ![![1,1],![2,2]], ![![1,2],![1,2]], ![![1,2],![2,1]], ![![2,0],![2,2]], ![![2,1],![1,2]], ![![2,1],![2,1]], ![![2,2],![0,2]], ![![2,2],![1,1]], ![![2,2],![2,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (79 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_79_2 :
    (1386294278918096471370420458492 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (79 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 2 ⟨(79 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 2 ⟨(79 : Fin 88), complement (htotal3 0 (79 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (79 : Fin 88)) (⟨![0,3,1], by decide +kernel⟩) = (⟨![1,3,0], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (79 : Fin 88)) (⟨![0,4,0], by decide +kernel⟩) = (⟨![1,2,1], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (79 : Fin 88)) (⟨![1,2,1], by decide +kernel⟩) = (⟨![0,4,0], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (79 : Fin 88)) (⟨![1,3,0], by decide +kernel⟩) = (⟨![0,3,1], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42232242412414726408440493659450000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42232242412414726408440493659450000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 2 ⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = 84464484824829452816880987318900000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (79 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42230357244875889090198562648500000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25817136173108185803119012681100000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 2 ⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = 25817136173108185803119012681100000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (79 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12929032066834773569987456505300000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(79 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 12908568086554092901559506340550000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12908568086554092901559506340550000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 2 ⟨(79 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = 25817136173108185803119012681100000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(79 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12888104106273412233131556175800000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 2 ⟨(79 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 84464484824829452816880987318900000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 2 ⟨(79 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = 84464484824829452816880987318900000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 2) ⟨(79 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (79 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42234127579953563726682424670400000000000000000000000000 := by decide +kernel
  have hn : n3 0 (79 : Fin 88) = 110281620997937638620000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (79 : Fin 88)
      ![![0,0],![0,1]] = ((100040531047 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (79 : Fin 88)
      ![![0,0],![1,0]] = ((100040531047 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (79 : Fin 88)
      ![![0,1],![0,0]] = ((99959468953 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (79 : Fin 88)
      ![![1,0],![0,0]] = ((99959468953 : ℚ)/400000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, hm0, hm1, hm2, hm3, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 2) (79 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 2) (79 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem mx_0_80_1 :
    (1386294361119860121800508000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (80 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hz : ∀ w : (Fin 2 → CompleteSplit.CompleteWord 2), w ∉ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2)) →
      ∀ x, mu3 0 1 ⟨(80 : Fin 88), x⟩ (w 0) = 0 ∨
        mu3 0 1 ⟨(80 : Fin 88), complement (htotal3 0 (80 : Fin 88)) x⟩ (w 1) = 0 := by
    decide +kernel
  have hS : ∀ g : ((Fin 2 → CompleteSplit.CompleteWord 2)) → ℚ,
      ∑ w ∈ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset ((Fin 2 → CompleteSplit.CompleteWord 2))), g w = g ![![0,0],![0,1]] + g ![![0,0],![1,0]] + g ![![0,1],![0,0]] + g ![![1,0],![0,0]] := by
    intro g
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hc0 : complement (htotal3 0 (80 : Fin 88)) (⟨![0,0,4], by decide +kernel⟩) = (⟨![2,1,1], by decide +kernel⟩) := by decide +kernel
  have hc1 : complement (htotal3 0 (80 : Fin 88)) (⟨![0,1,3], by decide +kernel⟩) = (⟨![2,0,2], by decide +kernel⟩) := by decide +kernel
  have hc2 : complement (htotal3 0 (80 : Fin 88)) (⟨![1,0,3], by decide +kernel⟩) = (⟨![1,1,2], by decide +kernel⟩) := by decide +kernel
  have hc3 : complement (htotal3 0 (80 : Fin 88)) (⟨![1,1,2], by decide +kernel⟩) = (⟨![1,0,3], by decide +kernel⟩) := by decide +kernel
  have hc4 : complement (htotal3 0 (80 : Fin 88)) (⟨![2,0,2], by decide +kernel⟩) = (⟨![0,1,3], by decide +kernel⟩) := by decide +kernel
  have hc5 : complement (htotal3 0 (80 : Fin 88)) (⟨![2,1,1], by decide +kernel⟩) = (⟨![0,0,4], by decide +kernel⟩) := by decide +kernel
  have hv0 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(80 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 41804542829927110005384961570000000000000000000000000000 else 0 := by decide +kernel
  have ht0 : ∑ v, mu3 0 1 ⟨(80 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = 41804542829927110005384961570000000000000000000000000000 := by decide +kernel
  have hf0 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(80 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht0, hv0 v]
    split_ifs <;> norm_num
  have hm0 : m3 0 (80 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20902495512528238143070082319500000000000000000000000000 := by decide +kernel
  have hv1 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 503236020973192744662270907984000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 503236020973192744662270907984000000000000000000000000000 else 0 := by decide +kernel
  have ht1 : ∑ v, mu3 0 1 ⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = 1006472041946385489324541815968000000000000000000000000000 := by decide +kernel
  have hf1 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht1, hv1 v]
    split_ifs <;> norm_num
  have hm1 : m3 0 (80 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 503235791124504480954684133718500000000000000000000000000 := by decide +kernel
  have hv2 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1795998183061080661170073222462000000000000000000000000000 else 0 := by decide +kernel
  have ht2 : ∑ v, mu3 0 1 ⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = 1795998183061080661170073222462000000000000000000000000000 := by decide +kernel
  have hf2 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht2, hv2 v]
    split_ifs <;> norm_num
  have hm2 : m3 0 (80 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 897998885937827286994739562509500000000000000000000000000 := by decide +kernel
  have hv3 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(80 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 897999091530540330585036611231000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 897999091530540330585036611231000000000000000000000000000 else 0 := by decide +kernel
  have ht3 : ∑ v, mu3 0 1 ⟨(80 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = 1795998183061080661170073222462000000000000000000000000000 := by decide +kernel
  have hf3 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(80 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht3, hv3 v]
    split_ifs <;> norm_num
  have hm3 : m3 0 (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 897999297123253374175333659952500000000000000000000000000 := by decide +kernel
  have hv4 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 1006472041946385489324541815968000000000000000000000000000 else 0 := by decide +kernel
  have ht4 : ∑ v, mu3 0 1 ⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = 1006472041946385489324541815968000000000000000000000000000 := by decide +kernel
  have hf4 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [ht4, hv4 v]
    split_ifs <;> norm_num
  have hm4 : m3 0 (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 503236250821881008369857682249500000000000000000000000000 := by decide +kernel
  have hv5 : ∀ v : CompleteSplit.CompleteWord 2, mu3 0 1 ⟨(80 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 20902271414963555002692480785000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 20902271414963555002692480785000000000000000000000000000 else 0 := by decide +kernel
  have ht5 : ∑ v, mu3 0 1 ⟨(80 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = 41804542829927110005384961570000000000000000000000000000 := by decide +kernel
  have hf5 : ∀ v : CompleteSplit.CompleteWord 2,
      freqQ (mu3 0 1) ⟨(80 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [ht5, hv5 v]
    split_ifs <;> norm_num
  have hm5 : m3 0 (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20902047317398871862314879250500000000000000000000000000 := by decide +kernel
  have hn : n3 0 (80 : Fin 88) = 2844274767837393260500000000000000000000000000000000000000 := by decide +kernel
  have hq0 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (80 : Fin 88)
      ![![0,0],![0,1]] = ((500000087317 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq1 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (80 : Fin 88)
      ![![0,0],![1,0]] = ((500000087317 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq2 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (80 : Fin 88)
      ![![0,1],![0,0]] = ((499999912683 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  have hq3 : mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (80 : Fin 88)
      ![![1,0],![0,0]] = ((499999912683 : ℚ)/2000000000000) := by
    simp only [mixQ, hsp, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, hm0, hm1, hm2, hm3, hm4, hm5, hn]
    norm_num
  rw [mme_certified_floor_support.{0} (mixQ (htotal3 0) (n3 0) (m3 0)
      (mu3 0 1) (80 : Fin 88)) _ ({![![0,0],![0,1]], ![![0,0],![1,0]], ![![0,1],![0,0]], ![![1,0],![0,0]]} : Finset (Fin 2 → CompleteSplit.CompleteWord 2))
      (fun w hw => (mme_certified_mixture_support.{0,0}).2 (htotal3 0) (n3 0) (m3 0)
        (mu3 0 1) (80 : Fin 88) w (hz w hw))]
  simp only [hS, hq0, hq1, hq2, hq3, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((1859688689610567111003463819947 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (77 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 5 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 7 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 11 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 13 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 15 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 19 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 21 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 29 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 31 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 33 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 37 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 39 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 45 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 55 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 57 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 63 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1167102278938330709868349066786 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (77 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 8 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 14 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 16 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 20 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 22 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 24 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 32 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 34 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 38 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 40 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else -2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 42 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 46 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 48 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 56 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 58 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 60 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 64 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 66 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 72 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1685792663679872345099737498522 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (78 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 17 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 23 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 25 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 35 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 41 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 43 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 47 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 49 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 51 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 59 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 61 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 65 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 67 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 69 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 73 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 75 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1897595367023868788626988830248 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (78 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 10 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 12 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 18 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 28 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 30 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 5) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 36 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 3) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 54 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1810284755295356136751912948110 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (79 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 7) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -8) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294278918096471370420458492 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 2) (79 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((1386294361119860121800508000000 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 0) (n3 0) (m3 0) (mu3 0 1) (80 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 9 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 27 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.mx_0_77_1, L3C.mx_0_77_2, L3C.mx_0_78_1, L3C.mx_0_78_2, L3C.mx_0_79_1, L3C.mx_0_79_2, L3C.mx_0_80_1⟩
