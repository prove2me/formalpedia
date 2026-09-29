-- Prove2me | solution 1 for mme_released_recursive_level3_penalty27
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T09:18:24.192824+00:00
-- url     : https://prove2.me/submissions/a5be9933-1a68-4a2f-bcd4-645e40a12ed2

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

theorem pn_4_32 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (32 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (32 : Fin 88)), (alphaG (n3 4) (m3 4) (32 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1375012969588896344910 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (32 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (32 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (32 : Fin 88) = 2852852408763104434800000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (32 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20987510230873599788156166883200000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (32 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((919584473 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (32 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 504722144531441866817631047328000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (32 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((2211480267 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (32 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 900716546212930974731066090637600000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (32 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((157862450831 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 900716508638011898912217579886800000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((315724888491 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (32 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 504722128937750600518502206711200000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (32 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((88459207947 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (32 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20987570212095494032426908553200000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (32 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7356696809 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_33 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (33 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (33 : Fin 88)), (alphaG (n3 4) (m3 4) (33 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11008108485457246696188 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (33 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (33 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (33 : Fin 88) = 111371395039279837175000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (33 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13242555760331624089457846493000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (33 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((2972611539 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (33 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42439025739950362204571054564175000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (33 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((381058580841 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (33 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42439849564851121681297502407975000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (33 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((381065977937 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13249963974146729199673596534850000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((59485489831 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_34 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (34 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (34 : Fin 88)), (alphaG (n3 4) (m3 4) (34 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (863736152598207363410663 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (34 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (34 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (34 : Fin 88) = 22343909623700462424900000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (34 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 36671116621035528815292085567500000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((65648523 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (34 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 246674173636691470601222688060300000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11039884147 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (34 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 271010465393707542298148365194000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((606452653 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (34 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7009455621468151132301780685443700000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313707660813 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (34 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3608144146607606149530289033048500000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((32296444153 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (34 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3608144224945353290224110294747900000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161482224271 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (34 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 7009461613836585293281397494524900000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313707929001 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (34 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 271007567031126794368964456865600000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((758057709 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (34 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 246670544807017304656521184901100000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11039721739 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 4 (34 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 36670149353187918822273711646500000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 4) (m3 4) (34 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((328233957 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_35 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (35 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (35 : Fin 88)), (alphaG (n3 4) (m3 4) (35 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10890342759558618305147 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (35 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (35 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (35 : Fin 88) = 3204803582879214136392000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (35 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23610280852199770788504257316504000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (35 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7367153787 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (35 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1010719023100029782933888286771264000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (35 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((39422034649 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (35 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 568072482285981299460642912548016000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (35 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((88628283699 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (35 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 568072490253123006498369255618528000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (35 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((44314142471 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (35 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1010718997852587157011439320275088000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (35 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((157688134657 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23610308535293119699155967470600000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((294686497 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_36 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (36 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (36 : Fin 88)), (alphaG (n3 4) (m3 4) (36 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3208780614452806058133695 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (36 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (36 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (36 : Fin 88) = 30945654421230948857778000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (36 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 331969068499244840077263509983512000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2681871451 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (36 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46556236429122113804124040771446000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1504451507 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (36 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5057895960289457468828825815943544000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40861116487 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (36 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9679345491796537061451872457322218000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((312785289981 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (36 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 357060320101559771536600803524988000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((5769151223 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (36 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 357060705560631242389299776007756000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((5769157451 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (36 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9679345395400823539317466765343748000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156392643433 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (36 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5057896262876066399625043747296828000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((81722237863 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (36 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46556241225698549094921113727036000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((752225831 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 4 (36 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 331968739051807871652581970078924000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 4) (m3 4) (36 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((5363737579 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_37 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (37 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (37 : Fin 88)), (alphaG (n3 4) (m3 4) (37 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2346372184157295718637 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (37 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (37 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (37 : Fin 88) = 10579856008931009917324000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (37 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3490911990642301430119012215260000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (37 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((65991673 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (37 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 717181964628405326023864612056348000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (37 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((67787497677 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (37 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4434176823637170156322427128020544000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (37 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((26194690291 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (37 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 135078366609277915560685740084800000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (37 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((31918763 : ℚ)/2500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (37 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 135078208726086694283224743858748000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (37 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12767490277 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (37 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4434176965883334196399855466441724000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (37 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((419115058101 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (37 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 717181836538088625896127543014680000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (37 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((6778748557 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (37 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3490930918004701407695754307896000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (37 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((164980077 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_38 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (38 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (38 : Fin 88)), (alphaG (n3 4) (m3 4) (38 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (368385957179627291862 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (38 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (38 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (38 : Fin 88) = 33099802441880096977626000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (38 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 405085390472394163445829530907864000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (38 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3059575591 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (38 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10723986060057735864365576537928000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (38 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((80997357 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (38 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 14061110126150946200617202405897562000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (38 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((424809487937 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (38 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2072981427176987714992029665413602000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (38 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((62628211477 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (38 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2072982123166533660404828813955504000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (38 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7828529063 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (38 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 14061110973605188120073325324056040000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (38 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((21240475677 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (38 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10724049975776251134832840333734000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (38 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((323991359 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (38 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 405084365272213131093585842897766000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (38 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12238271391 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_39 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)), (alphaG (n3 4) (m3 4) (39 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (15351676608591161263301 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (39 : Fin 88) = 7249411247529971479884000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (39 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1046491748960495844793378371862944000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (39 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((18044426527 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (39 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 260206853500211473531660110305664000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (39 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1121672353 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (39 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2383640077204276904243440301412000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (39 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((328804643 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (39 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 292113706797375505336996555192464000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (39 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((10073704499 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (39 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4047019542309936419088731985379572000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (39 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((558254926383 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (39 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 292113603616505219242912482003492000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (39 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((40294803763 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (39 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2383465562127315115240005053880000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (39 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((32878057 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (39 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 260206927458705020832429148082232000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (39 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((17946762749 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (39 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1046491759247410405038407901818340000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (39 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((28871082727 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_40 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)), (alphaG (n3 4) (m3 4) (40 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5693332430177811821896 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (40 : Fin 88) = 2069487094319678026602000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (40 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 362502642833087114018922031153530000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (40 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((35033090453 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (40 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14562237401603804228998883572476000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (40 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((3518320419 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (40 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 657678678452191210413685693447134000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (40 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((317797912467 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (40 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 657678659551565577992066276491068000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (40 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((158898951667 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (40 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14562233740681134377488454513538000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (40 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7036639069 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (40 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 362502642340549185570838660822254000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (40 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((175165452027 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_41 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)), (alphaG (n3 4) (m3 4) (41 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (944216630626505119884 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (41 : Fin 88) = 586212289303707866358000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (41 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 103093390073032994137022471768778000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (41 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((175863576991 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (41 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 185818318565258696324471367151248000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (41 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((39622659307 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (41 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 4194422336057108683394223215118000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (41 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7155125221 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (41 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4194369109739876774631081507792000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (41 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((894379303 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (41 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 185818425891935683493826079305678000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (41 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((316981457541 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (41 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 103093363327683506944654777051386000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (41 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((175863531367 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_42 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (42 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (42 : Fin 88)), (alphaG (n3 4) (m3 4) (42 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2164682889605391600613 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (42 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (42 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (42 : Fin 88) = 110217471991083150788000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (42 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42211591316485648642647844086280000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (42 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((38298457181 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (42 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12897142184063013289202871525764000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (42 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((117015405553 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (42 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12897147159279698966696298096084000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (42 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((117015450693 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (42 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42211591331254789889452986291872000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (42 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((47873071493 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_43 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (43 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (43 : Fin 88)), (alphaG (n3 4) (m3 4) (43 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (918707460825239987063 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (43 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (43 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (43 : Fin 88) = 110354343848059076483000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (43 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12883090971651018763563969385904000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (43 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7296433993 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (43 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42294047207234068523799091954009000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (43 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((383256750323 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (43 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42293832504250473304717186311835000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (43 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((76650960949 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (43 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12883373164923515890919752348252000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (43 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((29186375261 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_44 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (44 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (44 : Fin 88)), (alphaG (n3 4) (m3 4) (44 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4660062846245948152099 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (44 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (44 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (44 : Fin 88) = 393541014929840759542000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (44 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2815870781717958463101914087260000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (44 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((715521553 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (44 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 69187585162976898462916946203252000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (44 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((87903906503 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (44 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 124767101732123617743363649673268000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (44 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((158518549527 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (44 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 124767000725493184835504464864006000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (44 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((317036842393 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (44 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 69187587716271003327723794111748000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (44 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((87903909747 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (44 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 2815868811258096709389231060466000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (44 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((7155210523 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_45 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (45 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 3) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 3) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (45 : Fin 88)), (alphaG (n3 4) (m3 4) (45 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 3) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 3) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (305348373182614402223 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (45 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (45 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (45 : Fin 88) = 5915395272961903373937000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (45 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1944853601672450556047271167100000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (45 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3287783 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (45 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 75244449964619291955046960084605000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (45 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((2544021033 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (45 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 400816102965642469834647254463726000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (45 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((33879063399 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (45 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2479692282820820424356250870533475000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (45 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((16767719947 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (45 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2479691927861611675004277014069853000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (45 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((419192938669 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (45 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 400815488285088865817343861922182000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (45 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((33879011443 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (45 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 75245066053036970937283355623155000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (45 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2544041863 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (45 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1945101409411225476103412135904000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (45 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10275631 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_46 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (46 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (46 : Fin 88)), (alphaG (n3 4) (m3 4) (46 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13706047771413446818629 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (46 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (46 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (46 : Fin 88) = 2832800375735216448583000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (46 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20834789016985402677172471370196000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (46 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((1838709603 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (46 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 501046357057253048060948271703486000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (46 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((88436580521 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (46 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 894519038583806947845379020681779000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (46 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((315771999413 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (46 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 894519000768754732155974648547312000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (46 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((19735749129 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (46 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 501046341972591047270920682999011000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (46 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((176873155717 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (46 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20834848335825270572604904698216000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (46 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((919357419 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_47 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (47 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (47 : Fin 88)), (alphaG (n3 4) (m3 4) (47 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5063424112223239342384 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (47 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (47 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (47 : Fin 88) = 111384194560710480108000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (47 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13238262433257701939859525766308000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (47 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((118852252651 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (47 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42450208566787632981469864770936000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (47 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((190557595421 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (47 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42450935103277761000107381793012000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (47 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((381121713639 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (47 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13244788457387384186563227669744000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (47 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((29727710717 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (32 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (32 : Fin 88)), (alphaG (n3 4) (m3 4) (32 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1375012969588896344910 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (33 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (33 : Fin 88)), (alphaG (n3 4) (m3 4) (33 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11008108485457246696188 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (34 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (34 : Fin 88)), (alphaG (n3 4) (m3 4) (34 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (863736152598207363410663 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (35 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (35 : Fin 88)), (alphaG (n3 4) (m3 4) (35 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10890342759558618305147 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (36 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (36 : Fin 88)), (alphaG (n3 4) (m3 4) (36 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3208780614452806058133695 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (37 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (37 : Fin 88)), (alphaG (n3 4) (m3 4) (37 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2346372184157295718637 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (38 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (38 : Fin 88)), (alphaG (n3 4) (m3 4) (38 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (368385957179627291862 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (39 : Fin 88)), (alphaG (n3 4) (m3 4) (39 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (15351676608591161263301 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (40 : Fin 88)), (alphaG (n3 4) (m3 4) (40 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5693332430177811821896 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (41 : Fin 88)), (alphaG (n3 4) (m3 4) (41 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (944216630626505119884 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (42 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (42 : Fin 88)), (alphaG (n3 4) (m3 4) (42 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2164682889605391600613 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (43 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (43 : Fin 88)), (alphaG (n3 4) (m3 4) (43 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (918707460825239987063 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (44 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (44 : Fin 88)), (alphaG (n3 4) (m3 4) (44 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4660062846245948152099 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (45 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 3) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 3) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (45 : Fin 88)), (alphaG (n3 4) (m3 4) (45 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 3) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else 3) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (305348373182614402223 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (46 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (46 : Fin 88)), (alphaG (n3 4) (m3 4) (46 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13706047771413446818629 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (47 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (47 : Fin 88)), (alphaG (n3 4) (m3 4) (47 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5063424112223239342384 : ℚ)/10^30) :=
  ⟨L3C.pn_4_32, L3C.pn_4_33, L3C.pn_4_34, L3C.pn_4_35, L3C.pn_4_36, L3C.pn_4_37, L3C.pn_4_38, L3C.pn_4_39, L3C.pn_4_40, L3C.pn_4_41, L3C.pn_4_42, L3C.pn_4_43, L3C.pn_4_44, L3C.pn_4_45, L3C.pn_4_46, L3C.pn_4_47⟩
