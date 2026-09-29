-- Prove2me | solution 1 for mme_released_recursive_level3_penalty28
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T09:25:39.773997+00:00
-- url     : https://prove2.me/submissions/0c7034f5-e6bc-4fd7-a3fe-3faf0ef0c3df

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

theorem pn_4_48 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -1) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (48 : Fin 88)), (alphaG (n3 4) (m3 4) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -1) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (102422739315420524093 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (48 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (48 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (48 : Fin 88) = 18004967325945071968206000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5919082144371746614719412318050000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((13149887 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 715471936811958102270433011697074000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((39737474879 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 667269549483970273829635229801826000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((37060303271 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (48 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2598409595524283702186947173935736000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (48 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((36079065689 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (48 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10030826871278939311075168760292594000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (48 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((557114416799 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (48 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2598409809567335273021962731968664000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (48 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((36079068661 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (48 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 667269472440715086110672277848352000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (48 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2316268687 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (48 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 715471924262495876086717849857492000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (48 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((19868737091 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (48 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 5919084431002597009743552280212000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (48 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((164373651 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_49 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (49 : Fin 88)), (alphaG (n3 4) (m3 4) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (887337177287838425234027 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (49 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (49 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (49 : Fin 88) = 25400639798265866149852000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (49 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 41900322220381685133260321639768000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((824788717 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 281948178824080480130879552174356000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11100042403 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (49 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 308014291483058861805677627563624000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6063120731 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7966513680208332747683076950176484000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313634370767 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (49 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4101944319864584204174947369489868000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161489803109 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (49 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4101943958946893310615255246242800000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((1614897889 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (49 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 7966519598532005103831623999542632000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156817301883 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (49 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 308011396241932736067456268983108000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12126127479 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (49 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 281944678768320117884119299467868000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11099904609 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 4 (49 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 41899373176276902525703364719492000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 4) (m3 4) (49 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1649540071 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_50 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (50 : Fin 88)), (alphaG (n3 4) (m3 4) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3561946671661624240360 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (50 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (50 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (50 : Fin 88) = 3234276892914791088544000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (50 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23841450530557399195886371057344000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (50 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3685746663 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (50 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1019856650949369530680391278824256000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (50 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((157663781537 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (50 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 573442685804775522833261430369664000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (50 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((44325416839 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (50 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 573439243062565475219313274266144000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (50 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((177300602901 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (50 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1019864644645829875589794916278720000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (50 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((31533003463 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (50 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23832217921693285025352729203872000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (50 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7368638713 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_51 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (51 : Fin 88)), (alphaG (n3 4) (m3 4) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3311776212359386703558419 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (51 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (51 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (51 : Fin 88) = 35384309302883979821004000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (51 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 381660924811040994995805662687664000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2696540729 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (51 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 53141935011064456416109106386140000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((300370057 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5784938173519683387060871926854460000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((32697759473 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (51 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11067070412528955740893852191256524000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((312767738881 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (51 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 405343115978174176233124206033084000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11455448021 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 405343518474692496538394669953584000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((2863864849 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11067069871609019427706452667568376000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156383861797 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (51 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5784938334978286736120471850095712000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((20436100241 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (51 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 53142002948938317953350362713820000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((300370441 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 4 (51 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 381661013024124087085567356450636000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 4) (m3 4) (51 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10786165409 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_52 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else -7) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (52 : Fin 88)), (alphaG (n3 4) (m3 4) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else -7) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7149489440598870250416 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (52 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (52 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (52 : Fin 88) = 10444169626336467793416000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3432751363570080832176104630112000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((82169083 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 708306696765384556424996799942024000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((67818383089 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4377532775781715674661071580259328000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((3274503961 : ℚ)/7812500000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (52 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 132812651024382754943626045430760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (52 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((2543287897 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 132812521004915076680938485194976000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((3179106759 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4377532876735059282829369271418384000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((209568258337 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 708306584908327858361426732456664000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((67818372379 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (52 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3432768753112508682394980667752000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (52 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((328677997 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_53 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else 0) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (53 : Fin 88)), (alphaG (n3 4) (m3 4) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else 0) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2683287312739001885035 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (53 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (53 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (53 : Fin 88) = 39246437638786422208520000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (53 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 475404000993298270582201715775200000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (53 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((605665163 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (53 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12782688168999111696612809795400000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (53 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((65140629 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16839594538119155310769803614145960000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((429073198773 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (53 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2295437400510649858656068638288800000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (53 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((2924389497 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2295437854748919089970119279699280000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((29243900757 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16839594899971310340380616376700360000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((429073207993 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (53 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12782593663577277498908131679240000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (53 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((325700737 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (53 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 475403662610512948965669433915760000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (53 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((6056647319 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_54 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -3) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (54 : Fin 88)), (alphaG (n3 4) (m3 4) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -3) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6350766588589031411868 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (54 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (54 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (54 : Fin 88) = 1362867476596803749250000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (54 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 199191416504663105046784544523750000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (54 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((29231223127 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (54 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46309080561194824803100435070250000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (54 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((33979151573 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (54 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 434502771723981944901626152500000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (54 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((31881513 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 51485335470696743984804461215750000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((37777213379 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (54 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 768026843296920814387901324289750000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (54 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((563537435947 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (54 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 51485309524425724534854682994250000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (54 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((37777194341 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 434458692501186374477964159750000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((318782787 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 46309105652947936426854262512000000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((530924531 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (54 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 199191424121729431746320699082000000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (54 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((18269515153 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_55 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (55 : Fin 88)), (alphaG (n3 4) (m3 4) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3257551899030965038490 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (55 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (55 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (55 : Fin 88) = 2331298842478376446770000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (55 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 401652198796347388554496324046310000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (55 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((172286877803 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (55 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15462129636945767762924616914730000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (55 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((6632409949 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 748535070789108798701791895743080000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((80270175701 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (55 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 748535060246975433014573603449140000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (55 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((160540349141 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (55 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15462217459304462765843743187400000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (55 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((331622381 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (55 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 401652165549694595970369816659340000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (55 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((86143431771 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_56 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)), (alphaG (n3 4) (m3 4) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11047007231840531106567 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (56 : Fin 88) = 109659994126070730500000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (56 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42316252933769520577467087970000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (56 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((19294298377 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (56 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12543069868647153666436341314500000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (56 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((114381456689 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (56 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12529141957069941193872294804000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (56 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((14281805841 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (56 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42271529366584115062224275911500000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (56 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((385478129043 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_57 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)), (alphaG (n3 4) (m3 4) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2146517244341694746798 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (57 : Fin 88) = 110788246444993592814000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13129833437108656345036039771512000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((29628218377 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42264275308466400601761200037480000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((19074349791 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42264316824367567427100222413328000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((47685921319 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (57 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13129820875050968440102537777680000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (57 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((2962819003 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_58 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)), (alphaG (n3 4) (m3 4) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2099903874059368132739 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (58 : Fin 88) = 925028797380252713577000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (58 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6769109057393498138798175969840000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (58 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((91471599 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (58 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 163731251819226549759043018621059000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (58 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((177001248267 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 292014015949525654011005667303129000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((315681000177 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 292014075663834640095839339552787000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((315681064731 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 163731257370324362837939552796636000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((44250313567 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (58 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6769087519948008734374245756549000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (58 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((7317704637 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_59 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (59 : Fin 88)), (alphaG (n3 4) (m3 4) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10843634521950106143861 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (59 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (59 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (59 : Fin 88) = 1323357534643892744457000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (59 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 430225497051953408115910729731000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (59 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((325101483 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (59 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 16032073592338539622702044499269000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (59 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((12114695517 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (59 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 81408497625430281578647201582719000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (59 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((61516631367 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (59 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 563807971207929918347362149171759000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (59 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((426043572087 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (59 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 563807913367942151666741967189660000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (59 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((21302176419 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 81408396613549662210314017179909000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((61516555037 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (59 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 16032187956896683547913020473209000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (59 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12114781937 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (59 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 430268782753554075203689173744000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (59 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((20320887 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_60 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (60 : Fin 88)), (alphaG (n3 4) (m3 4) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (767002622384694538578 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (60 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (60 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (60 : Fin 88) = 3442557872355166768400000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (60 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22787638614585852910373770682400000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (60 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3309695793 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (60 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 593630369268111106745764291853600000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (60 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((86219373977 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (60 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1104860970466220360894654850364000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (60 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((32094187271 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (60 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1104860815647507725338094941879200000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (60 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((160470913869 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (60 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 593630321179020187816439704074000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (60 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((34487746797 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (60 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22787757179721534694672441146800000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (60 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6619426027 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_61 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -5) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (61 : Fin 88)), (alphaG (n3 4) (m3 4) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -5) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11758922593099710937115 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (61 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (61 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (61 : Fin 88) = 109646617331017308087000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (61 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12650905353408233853065884702488000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (61 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((14422361653 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (61 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42218176930625716291093616267292000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (61 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((96259642929 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (61 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42211019504263943661449813389152000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (61 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12030415453 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12566515542719414281390685641068000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((28652310141 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_62 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (62 : Fin 88)), (alphaG (n3 4) (m3 4) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8271664157935317190684 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (62 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (62 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (62 : Fin 88) = 28849530224411760060120000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9696811607435381327304781655280000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((168058397 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1193699340572655771554408853190200000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((8275346817 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (62 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1110315105861912608248302705470400000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (62 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((962160473 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (62 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4125677610137721745832263041943440000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (62 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((71503375931 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (62 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15970752455048446469468387726704080000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (62 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((276793977767 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (62 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4125677652459982585044315050139480000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (62 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143006753329 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (62 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1110315119507740404395065213907160000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (62 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((38486419393 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (62 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1193699366941126396666757548139880000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (62 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((41376734999 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (62 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9696762274738697583195078850080000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (62 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((84028771 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_63 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (63 : Fin 88)), (alphaG (n3 4) (m3 4) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868355300454968362921287 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (63 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (63 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (63 : Fin 88) = 36331063141478532832742000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (63 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 59570635132798408040951139501530000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((327932243 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 407234983865764651694323339919366000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11209002673 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (63 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 433645130825081206720656515695024000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((1491991609 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 11398574059901685002479024488890494000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313741825157 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5866507674049884955933053135632788000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((80736801607 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (63 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5866507277096689072138603405093696000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((5046049759 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11398580024154334560160888443148182000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313741989321 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (63 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 433641650309232253077211139011424000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((745989817 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (63 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 407232017616114465679510210698776000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2802230257 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 4 (63 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 59569688526948256817778182408720000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 4) (m3 4) (63 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((40990879 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -1) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (48 : Fin 88)), (alphaG (n3 4) (m3 4) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -1) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (102422739315420524093 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (49 : Fin 88)), (alphaG (n3 4) (m3 4) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (887337177287838425234027 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (50 : Fin 88)), (alphaG (n3 4) (m3 4) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3561946671661624240360 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (51 : Fin 88)), (alphaG (n3 4) (m3 4) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3311776212359386703558419 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else -7) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (52 : Fin 88)), (alphaG (n3 4) (m3 4) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else -7) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7149489440598870250416 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else 0) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (53 : Fin 88)), (alphaG (n3 4) (m3 4) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else 0) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 6 else if k.val = 2 then 7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2683287312739001885035 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -3) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (54 : Fin 88)), (alphaG (n3 4) (m3 4) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -3) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6350766588589031411868 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (55 : Fin 88)), (alphaG (n3 4) (m3 4) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3257551899030965038490 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (56 : Fin 88)), (alphaG (n3 4) (m3 4) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11047007231840531106567 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (57 : Fin 88)), (alphaG (n3 4) (m3 4) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2146517244341694746798 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (58 : Fin 88)), (alphaG (n3 4) (m3 4) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2099903874059368132739 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (59 : Fin 88)), (alphaG (n3 4) (m3 4) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10843634521950106143861 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (60 : Fin 88)), (alphaG (n3 4) (m3 4) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (767002622384694538578 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -5) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (61 : Fin 88)), (alphaG (n3 4) (m3 4) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -5) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11758922593099710937115 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (62 : Fin 88)), (alphaG (n3 4) (m3 4) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8271664157935317190684 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (63 : Fin 88)), (alphaG (n3 4) (m3 4) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868355300454968362921287 : ℚ)/10^30) :=
  ⟨L3C.pn_4_48, L3C.pn_4_49, L3C.pn_4_50, L3C.pn_4_51, L3C.pn_4_52, L3C.pn_4_53, L3C.pn_4_54, L3C.pn_4_55, L3C.pn_4_56, L3C.pn_4_57, L3C.pn_4_58, L3C.pn_4_59, L3C.pn_4_60, L3C.pn_4_61, L3C.pn_4_62, L3C.pn_4_63⟩
