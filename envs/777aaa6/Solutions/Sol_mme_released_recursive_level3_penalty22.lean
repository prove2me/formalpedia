-- Prove2me | solution 1 for mme_released_recursive_level3_penalty22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T10:00:50.129986+00:00
-- url     : https://prove2.me/submissions/a322a768-f420-4d8c-8fe7-6a923a9e2632

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_generic_rate_data
import Definitions.Def_mme_certified_entropy_rational_data
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3C

theorem pn_3_48 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (48 : Fin 88)), (alphaG (n3 3) (m3 3) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3352369472596796328054912 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (48 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (48 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (48 : Fin 88) = 36015497709394806725364000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 391724685966690455898387182828184000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5438279503 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (48 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 54834083848795518889314726288024000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((761256783 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5886675248726533069835728814179980000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((32689678739 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11259709866592391920291056105508224000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((9769847863 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (48 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 414801966950948365522476477598908000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11517318747 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (48 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 414818311720211829330033422641572000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11517772573 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (48 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11259678861966894331293185248126908000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312634270747 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (48 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5886674757619206304528144307116476000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((163448380059 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (48 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 54838720592017119504916969825476000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1522642309 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 3 (48 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 391741205411117810270756745886248000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 3) (m3 3) (48 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((5438508841 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_49 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (49 : Fin 88)), (alphaG (n3 3) (m3 3) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9613466498169341661918 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (49 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (49 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (49 : Fin 88) = 28010207809801538096205000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9408455588187240833803672568280000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((41986727 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1158863873040357623696498404074825000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((8274582473 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (49 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1078043166262581842670389190477735000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (49 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((38487510467 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (49 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4005717071930006662358196812400525000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (49 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((28601837581 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (49 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15506143223674803415277889007476405000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (49 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((553589010441 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (49 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4005716685725261380814589541925985000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (49 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143009174117 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (49 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1078043776016795654240072006764380000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (49 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((9621883059 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (49 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1158864420751961136555774337267395000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (49 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((41372931919 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (49 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9407136811583139757787027044470000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (49 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((167923367 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_50 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (50 : Fin 88)), (alphaG (n3 3) (m3 3) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1186411956567645302375 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (50 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (50 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (50 : Fin 88) = 900766886204704707508000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (50 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6590475895463904487083930197976000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (50 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((3658258311 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (50 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 159431857051978045909033048479432000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (50 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((88497845277 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 284361098426024778086423024860924000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((315687779803 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (50 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 284361169411860012334382204736372000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (50 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((315687858609 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (50 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 159431837553978027121994949761264000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (50 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((44248917227 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (50 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6590447865399939569082841964032000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (50 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((57160043 : ℚ)/7812500000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_51 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (51 : Fin 88)), (alphaG (n3 3) (m3 3) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868175482387996737542350 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (51 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (51 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (51 : Fin 88) = 36591221904372441633275000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (51 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 60000137737472921223548030124225000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1639741299 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (51 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 410147443914519754279579384245825000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11208902643 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (51 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 436777371213162017308536133134800000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((746041927 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 11480181873488427115955306642773850000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((156870709367 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (51 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5908504096449887818659459178201475000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161473265689 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5908504162862955575095440742595600000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((10092079219 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11480181946853827034222052117490225000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313741420739 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (51 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 436777408792346913099033690508225000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((11936671859 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (51 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 410147336446101021137718307317150000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((5604449853 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 3 (51 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 60000126613741462294325773608625000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 3) (m3 3) (51 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((327948199 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_52 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (52 : Fin 88)), (alphaG (n3 3) (m3 3) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (45917398148188764437088 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (52 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (52 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (52 : Fin 88) = 6599317695239016910160000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2152953102953116266087325418720000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((163119371 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 405323243515333613170200415498560000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((15354740529 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 2811883783264229550356150053321440000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((213043523067 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (52 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 80298882308285646375311543394560000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (52 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((760484701 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 80298923910384397162074145043200000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((152097019 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2811883692035261731371980287269600000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((42608703231 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 405323268638936078945137792477680000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((61418965923 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (52 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2152948463632776513058437576240000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (52 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((326238039 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_53 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (53 : Fin 88)), (alphaG (n3 3) (m3 3) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5472126581682100081203 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (53 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (53 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (53 : Fin 88) = 34396559660446589688750000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11036837650492003449385549867500000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((160435197 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1247678141608241482376684069201250000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((36273341111 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5046863749191557562001834848476250000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((146725829531 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1262396472482646153662737305138750000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((36701242361 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19260609202617512718222115031036250000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((559957431579 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1262397717603709302168837448200000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((229382991 : ℚ)/6250000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (53 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5046863752218454812121134741086250000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (53 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((146725829619 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1247679374449732832103351693378750000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((36273376953 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11034412624242822643919313615000000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((80199973 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_54 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (54 : Fin 88)), (alphaG (n3 3) (m3 3) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10308897326853363232347 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (54 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (54 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (54 : Fin 88) = 1237144805309001638184000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (54 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 402160275098623285462609071936000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (54 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((40633913 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (54 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 14984699734989722727523727841432000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (54 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((12112324823 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (54 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 76110358421983771692603918966672000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (54 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((30760489029 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 527075191898912218328764909051680000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((21302081601 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 527075159460975423126741955867200000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((2130208029 : ℚ)/5000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 76110321428879803342836933988704000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((15380237039 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (54 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 14984752862936241917290078015128000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (54 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12112367767 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (54 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 402161225225833762775867197248000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (54 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((40634009 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_55 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (55 : Fin 88)), (alphaG (n3 3) (m3 3) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4082620728983739488022 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (55 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (55 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (55 : Fin 88) = 3886598240267698714202000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (55 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25588611845410543809560409889560000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (55 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((329190339 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1245739873611487745157186041916860000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((32052190543 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 671970552106171453646994364972090000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((34578853309 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 671970703605770859281890244566050000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6915772221 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1245739622805416702442320315747598000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((320521840899 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25588876293441409864048622907842000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((6583874821 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_56 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (56 : Fin 88)), (alphaG (n3 3) (m3 3) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (816385940221217526919 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (56 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (56 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (56 : Fin 88) = 3447862528609935130484000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22795630562937624306199550726660000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((1322305073 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 594567107895144669548358832221996000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((172445131719 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1106568563428586833235734539326944000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((40117919227 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1106568405692324011859812254814428000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((320943308067 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (56 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 594567011403263943870714270496772000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (56 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((172445103733 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (56 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22795809627678047663180552413200000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (56 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((66115773 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_57 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (57 : Fin 88)), (alphaG (n3 3) (m3 3) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (455062585871701633691 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (57 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (57 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (57 : Fin 88) = 109592202135686874520000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (57 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12571857183914974623555721927720000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (57 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((114714887911 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (57 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42224480967807924427659159674840000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (57 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((385287275417 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (57 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42224480874764144814461003207360000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (57 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((48160909321 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (57 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12571383109199830654324115190080000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (57 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((14338820263 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_58 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (58 : Fin 88)), (alphaG (n3 3) (m3 3) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5006651548342167903955 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (58 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (58 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (58 : Fin 88) = 110855027061218995692000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42279941068206625353780733849764000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((381398500267 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (58 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13146851513076163961460556370400000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (58 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((592974981 : ℚ)/5000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13146159435941253525189274571964000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((118588753117 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42282075043994952851569435207872000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((23838609401 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_59 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (59 : Fin 88)), (alphaG (n3 3) (m3 3) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6402531869965365827585 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (59 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (59 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (59 : Fin 88) = 1785641789345352310851000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 314464949247743581153826540189286000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((88053760593 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12958074801796518637042018152351000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7256816501 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 565397987463035257869069197571846000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((158317863873 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 565397854298798817439420615858521000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((316635653171 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12957913319066940979451138653017000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7256726067 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (59 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 314465010214911194772190489574979000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (59 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((176107555329 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_60 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (60 : Fin 88)), (alphaG (n3 3) (m3 3) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6140796380164363752738 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (60 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (60 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (60 : Fin 88) = 30125259808517853422898000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (60 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 373147124146075138841474214936396000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (60 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((6193259851 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (60 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 9782804147840909958453733644228000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (60 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((162368793 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (60 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12710937165795345327980027461769388000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (60 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((210968092003 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (60 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 1968762889338848111453963385025932000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (60 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((32676280667 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (60 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1968762207363216566226797597461008000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (60 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((8169067337 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (60 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 12710936716446970024127725805822820000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (60 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((42193616909 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (60 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9783018338438148520391570449008000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (60 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((40593087 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (60 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 373147882941119195789166230891220000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (60 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1238654489 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_61 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (61 : Fin 88)), (alphaG (n3 3) (m3 3) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13503918259768392195439 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (61 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (61 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (61 : Fin 88) = 109648849316159623379000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (61 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12517544539059353799111306262881000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (61 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((114160290939 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (61 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42264369016500839623897972288981000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (61 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((385452006839 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (61 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42255800361447707588952880863290000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (61 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((38537386051 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (61 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12611135399151722367037840584848000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (61 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((7188365107 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_62 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (62 : Fin 88)), (alphaG (n3 3) (m3 3) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (21526383440989311811290 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (62 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (62 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (62 : Fin 88) = 1053112676269650428709000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 186417451060846385009852790265761000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((177015674829 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (62 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 332424491553145978489998921501108000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (62 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((78914749353 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (62 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7714437144058267736311832527647000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (62 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7325367283 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7714278893869517372211560854926000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((3662608507 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (62 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 332424626157795808571638117370652000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (62 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((78914781307 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (62 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 186417391459934471528986777479906000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (62 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((88507809117 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_63 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -3) else if j.val = 2 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (63 : Fin 88)), (alphaG (n3 3) (m3 3) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -3) else if j.val = 2 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14506429605730659706811 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (63 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (63 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (63 : Fin 88) = 7098599576199900135840000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1015637034804933546198167875649760000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((143075690339 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 264345289019394077860357382074080000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((37239075987 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (63 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2383509401010686952033438323520000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (63 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((167885889 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 297785583363139342839097600611840000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((2621869111 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3938296692587394839240396941538400000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((110959821027 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (63 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 297785621305154077627563826676640000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (63 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((41949911121 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (63 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2383522519222703769448889355840000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (63 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((167886813 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 264345315028662925056791479791840000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((37239079651 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (63 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1015637008170987936296142565978080000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (63 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143075686587 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (48 : Fin 88)), (alphaG (n3 3) (m3 3) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3352369472596796328054912 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (49 : Fin 88)), (alphaG (n3 3) (m3 3) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9613466498169341661918 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (50 : Fin 88)), (alphaG (n3 3) (m3 3) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1186411956567645302375 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (51 : Fin 88)), (alphaG (n3 3) (m3 3) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868175482387996737542350 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (52 : Fin 88)), (alphaG (n3 3) (m3 3) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (45917398148188764437088 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (53 : Fin 88)), (alphaG (n3 3) (m3 3) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5472126581682100081203 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (54 : Fin 88)), (alphaG (n3 3) (m3 3) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10308897326853363232347 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (55 : Fin 88)), (alphaG (n3 3) (m3 3) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4082620728983739488022 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (56 : Fin 88)), (alphaG (n3 3) (m3 3) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (816385940221217526919 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (57 : Fin 88)), (alphaG (n3 3) (m3 3) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (455062585871701633691 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (58 : Fin 88)), (alphaG (n3 3) (m3 3) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5006651548342167903955 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (59 : Fin 88)), (alphaG (n3 3) (m3 3) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6402531869965365827585 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (60 : Fin 88)), (alphaG (n3 3) (m3 3) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6140796380164363752738 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (61 : Fin 88)), (alphaG (n3 3) (m3 3) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13503918259768392195439 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (62 : Fin 88)), (alphaG (n3 3) (m3 3) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (21526383440989311811290 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -3) else if j.val = 2 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (63 : Fin 88)), (alphaG (n3 3) (m3 3) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -3) else if j.val = 2 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14506429605730659706811 : ℚ)/10^30) :=
  ⟨L3C.pn_3_48, L3C.pn_3_49, L3C.pn_3_50, L3C.pn_3_51, L3C.pn_3_52, L3C.pn_3_53, L3C.pn_3_54, L3C.pn_3_55, L3C.pn_3_56, L3C.pn_3_57, L3C.pn_3_58, L3C.pn_3_59, L3C.pn_3_60, L3C.pn_3_61, L3C.pn_3_62, L3C.pn_3_63⟩
