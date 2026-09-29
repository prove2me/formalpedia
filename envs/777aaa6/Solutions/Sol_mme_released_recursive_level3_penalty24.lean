-- Prove2me | solution 1 for mme_released_recursive_level3_penalty24
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T10:00:50.423238+00:00
-- url     : https://prove2.me/submissions/22ac5ac3-b022-4786-b22d-bd5faece2a43

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

theorem pn_3_80 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else 8) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (80 : Fin 88)), (alphaG (n3 3) (m3 3) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else 8) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1801970154271129307248 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (80 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (80 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (80 : Fin 88) = 401106973145735345902000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2871261758351944469097426286418000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7158344159 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 70541518582172376081124656188748000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((87933548037 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 127141790880951500763264714267310000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((63395452781 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (80 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 127139357351307788499966125072642000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (80 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((316971196871 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (80 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 70542726918132298528291392001454000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (80 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((175870108577 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (80 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 2870317654819437560255686183428000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (80 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((3577995207 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_81 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)), (alphaG (n3 3) (m3 3) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (807974854670003444941075 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (81 : Fin 88) = 32853313869175885690960000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (81 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 53422813008083609125605228079120000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1626101197 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 365053188023113696386935719000880000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11111609303 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (81 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 392535375207781521231066339150880000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((5974060589 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10309276952290775746608236729763360000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((156898585533 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5306368533419511307380272721293200000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((32303399009 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5306368525928955745208170783754320000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161516994817 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10309276796828894517667945640140640000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156898583167 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 392535506621036997934609102990880000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((5974062589 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (81 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 365053325809912063710600306887120000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11111613497 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 3 (81 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 53422852037820485706557428939600000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 3) (m3 3) (81 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((325220477 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_82 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)), (alphaG (n3 3) (m3 3) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (12739121491175772970180 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (82 : Fin 88) = 7110696474221266326825000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2333834100358691321659150918350000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((164107279 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 436357839991447962870139210441500000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((3068319971 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (82 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3029564738793591886312049831946000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (82 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5325717301 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87091655879495595720171519112275000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12247978267 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87091930601253877258796055996150000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6124008451 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3029564535385008544738505286790050000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((213028677737 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (82 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 436358097910630475823911417037900000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (82 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((15341608923 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (82 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2333841559479292779767527757775000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (82 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((328215607 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_83 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)), (alphaG (n3 3) (m3 3) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8154290645077553439977 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (83 : Fin 88) = 34763075447437485171880000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (83 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11151468881547953646050849658760000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (83 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((320784877 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (83 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1261942269466189564170934950225360000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (83 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((18150613161 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (83 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5100665653901964040478311550931840000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (83 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((9170408523 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (83 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1274975275449179911910232428897680000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (83 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((18338067893 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19465606102271298030739007107274440000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((559950633013 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1274975488859700083728953899069000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((1467045677 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5100665662523206751442807873558080000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((18340817077 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1261942486596358808865467333787840000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((4537654071 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11151039488040026898234006597000000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12830901 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_84 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (84 : Fin 88)), (alphaG (n3 3) (m3 3) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4137090697166625403212 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (84 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (84 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (84 : Fin 88) = 740055869715957805808000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (84 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 239360842747451208035763527632000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (84 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((323436179 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 8914735696711393220029494073280000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((602301533 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 45555970433703328373767920320736000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((30778737321 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 315317873803043520220681395124928000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((106518266629 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 315317850727361446607401052225680000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((85214607067 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 45555948396319639971976378970112000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((240458769 : ℚ)/3906250000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (84 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 8914768954082122385457329278992000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (84 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12046075599 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (84 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 239360861988903820650666478640000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (84 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((64687241 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_85 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (85 : Fin 88)), (alphaG (n3 3) (m3 3) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7928150910145582476000 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (85 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (85 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (85 : Fin 88) = 3858268195921083954800000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (85 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25425327631825367973091393380800000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (85 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((1647457249 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (85 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1236748763850050777923657296840800000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (85 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((160272523973 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (85 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 666960302045159248233808751187200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (85 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10804074979 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (85 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 666959574746171244325798935568000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (85 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((4321625279 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1236749463041554974546570501742000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((64109045833 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25424764606322341797073121281200000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((6589683069 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_86 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (86 : Fin 88)), (alphaG (n3 3) (m3 3) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1895673466415600117689 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (86 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (86 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (86 : Fin 88) = 3459033006866088870634000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (86 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22871431227797828002553820670414000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (86 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((6612088171 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (86 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 596588525952424672244639937969990000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (86 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((34494526347 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (86 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1110056236544842632307673120273772000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (86 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((160457595279 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (86 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1110056615630646953782950719665734000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (86 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((320915300151 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (86 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 596589104140168868931992931054992000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (86 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((21559099861 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22871093370207915364189470365098000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6611990497 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_87 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (87 : Fin 88)), (alphaG (n3 3) (m3 3) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (620669168485821055483 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (87 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (87 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (87 : Fin 88) = 109604683237731443642000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (87 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12572668945297094669779764510152000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (87 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((28677307789 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (87 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42229374181544926992055461605506000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (87 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((385288045493 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (87 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42229374293560913261016997007630000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (87 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((77057609303 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (87 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12573265817328508719147776876712000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (87 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((28678669209 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else 8) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (80 : Fin 88)), (alphaG (n3 3) (m3 3) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else 8) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1801970154271129307248 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (81 : Fin 88)), (alphaG (n3 3) (m3 3) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (807974854670003444941075 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (82 : Fin 88)), (alphaG (n3 3) (m3 3) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (12739121491175772970180 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (83 : Fin 88)), (alphaG (n3 3) (m3 3) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8154290645077553439977 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (84 : Fin 88)), (alphaG (n3 3) (m3 3) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4137090697166625403212 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (85 : Fin 88)), (alphaG (n3 3) (m3 3) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7928150910145582476000 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (86 : Fin 88)), (alphaG (n3 3) (m3 3) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1895673466415600117689 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (87 : Fin 88)), (alphaG (n3 3) (m3 3) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (620669168485821055483 : ℚ)/10^30) :=
  ⟨L3C.pn_3_80, L3C.pn_3_81, L3C.pn_3_82, L3C.pn_3_83, L3C.pn_3_84, L3C.pn_3_85, L3C.pn_3_86, L3C.pn_3_87⟩
