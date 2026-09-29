-- Prove2me | solution 1 for mme_released_recursive_level2_pen1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T02:35:06.231172+00:00
-- url     : https://prove2.me/submissions/d1aae1d6-988f-4c90-9d86-e0281bc77018

import Mathlib
import Definitions.Def_mme_released_recursive_level2_penalty_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_marginals
import Theorems.Thm_mme_released_recursive_level2_penalty_tools

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace MME.L2Cert

theorem alphaQ_jwv (r : Fin 1104)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)) :
    alphaQ r c = (jwv r c.val : ℚ) / (D : ℚ) :=
  (mme_released_recursive_level2_penalty_tools.1 r c).2

theorem PE_sum (r : Fin 1104) (a : Tri) (k : Fin 4) :
    ∑ i, PE r i (a i) k = PE r (certMode r) (a (certMode r)) k :=
  mme_released_recursive_level2_penalty_tools.2.2.1 r a k

theorem sum_triP (g : Tri → ℚ) :
    ∑ a : Tri, g a = ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, g ![x, y, z] :=
  mme_released_recursive_level2_penalty_tools.2.2.2.1 g

theorem jwv_112 (r : Fin 1104) (hp : parent2 r = ![1, 1, 2]) :
    jwv r ![0, 0, 2] = (l2At r).2.2 ∧ jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧ jwv r ![1, 1, 0] = (l2At r).2.2 :=
  mme_released_recursive_level2_penalty_tools.2.2.2.2.1 r hp

theorem jwv_121 (r : Fin 1104) (hp : parent2 r = ![1, 2, 1]) :
    jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧ jwv r ![0, 2, 0] = (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = (l2At r).2.2 ∧ jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2 :=
  mme_released_recursive_level2_penalty_tools.2.2.2.2.2.1 r hp

theorem jwv_211 (r : Fin 1104) (hp : parent2 r = ![2, 1, 1]) :
    jwv r ![0, 1, 1] = (l2At r).2.2 ∧ jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2 ∧ jwv r ![2, 0, 0] = (l2At r).2.2 :=
  mme_released_recursive_level2_penalty_tools.2.2.2.2.2.2.1 r hp

end MME.L2Cert

namespace MME.L2Cert

theorem pcert_46 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 46),
        qvalQ (fun t ↦ ∑ i, PE 46 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 46),
        (alphaQ 46 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 46 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 46 = 2 := by decide +kernel
  have hce : certE (46 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (37 : Int) else if j.val = 1 then -1 else if j.val = 2 then -8 else -6) else (if j.val = 0 then -23 else if j.val = 1 then -2 else if j.val = 2 then 0 else 6)) := by decide +kernel
  have hs : (l2At (46 : Fin 1104)).2.2 = 1558291252 := by decide +kernel
  have hp : parent2 (46 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 46 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 46 c] :
    ∀ c ∈ Finset.univ, (alphaQ 46 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 46 i (c.val i) t) =
      ((jwv 46 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 46 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 46 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 46 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 46 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_47 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 47),
        qvalQ (fun t ↦ ∑ i, PE 47 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 47),
        (alphaQ 47 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 47 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 47 = 1 := by decide +kernel
  have hce : certE (47 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 1 else if j.val = 1 then -2 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hs : (l2At (47 : Fin 1104)).2.2 = 21079978622 := by decide +kernel
  have hp : parent2 (47 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 47 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 47 c] :
    ∀ c ∈ Finset.univ, (alphaQ 47 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 47 i (c.val i) t) =
      ((jwv 47 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 47 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 47 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 47 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 47 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_48 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 48),
        qvalQ (fun t ↦ ∑ i, PE 48 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 48),
        (alphaQ 48 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 48 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 48 = 0 := by decide +kernel
  have hce : certE (48 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (48 : Fin 1104)).2.2 = 21076561725 := by decide +kernel
  have hp : parent2 (48 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 48 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 48 c] :
    ∀ c ∈ Finset.univ, (alphaQ 48 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 48 i (c.val i) t) =
      ((jwv 48 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 48 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 48 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 48 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 48 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_49 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 49),
        qvalQ (fun t ↦ ∑ i, PE 49 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 49),
        (alphaQ 49 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 49 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 49 = 2 := by decide +kernel
  have hce : certE (49 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -24 else if j.val = 1 then 6 else if j.val = 2 then 0 else 3)) := by decide +kernel
  have hs : (l2At (49 : Fin 1104)).2.2 = 14902773193 := by decide +kernel
  have hp : parent2 (49 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 49 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 49 c] :
    ∀ c ∈ Finset.univ, (alphaQ 49 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 49 i (c.val i) t) =
      ((jwv 49 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 49 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 49 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 49 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 49 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_50 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 50),
        qvalQ (fun t ↦ ∑ i, PE 50 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 50),
        (alphaQ 50 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 50 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 50 = 1 := by decide +kernel
  have hce : certE (50 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (50 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (50 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 50 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 50 c] :
    ∀ c ∈ Finset.univ, (alphaQ 50 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 50 i (c.val i) t) =
      ((jwv 50 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 50 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 50 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 50 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 50 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_51 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 51),
        qvalQ (fun t ↦ ∑ i, PE 51 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 51),
        (alphaQ 51 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 51 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 51 = 0 := by decide +kernel
  have hce : certE (51 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (51 : Fin 1104)).2.2 = 21076506959 := by decide +kernel
  have hp : parent2 (51 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 51 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 51 c] :
    ∀ c ∈ Finset.univ, (alphaQ 51 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 51 i (c.val i) t) =
      ((jwv 51 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 51 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 51 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 51 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 51 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_52 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 52),
        qvalQ (fun t ↦ ∑ i, PE 52 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 52),
        (alphaQ 52 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 52 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 52 = 2 := by decide +kernel
  have hce : certE (52 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (37 : Int) else if j.val = 1 then -1 else if j.val = 2 then -8 else -6) else (if j.val = 0 then -23 else if j.val = 1 then -2 else if j.val = 2 then 0 else 6)) := by decide +kernel
  have hs : (l2At (52 : Fin 1104)).2.2 = 1558231838 := by decide +kernel
  have hp : parent2 (52 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 52 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 52 c] :
    ∀ c ∈ Finset.univ, (alphaQ 52 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 52 i (c.val i) t) =
      ((jwv 52 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 52 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 52 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 52 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 52 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_53 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 53),
        qvalQ (fun t ↦ ∑ i, PE 53 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 53),
        (alphaQ 53 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 53 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 53 = 1 := by decide +kernel
  have hce : certE (53 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hs : (l2At (53 : Fin 1104)).2.2 = 21067840867 := by decide +kernel
  have hp : parent2 (53 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 53 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 53 c] :
    ∀ c ∈ Finset.univ, (alphaQ 53 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 53 i (c.val i) t) =
      ((jwv 53 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 53 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 53 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 53 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 53 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_54 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 54),
        qvalQ (fun t ↦ ∑ i, PE 54 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 54),
        (alphaQ 54 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 54 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 54 = 0 := by decide +kernel
  have hce : certE (54 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hs : (l2At (54 : Fin 1104)).2.2 = 21088725348 := by decide +kernel
  have hp : parent2 (54 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 54 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 54 c] :
    ∀ c ∈ Finset.univ, (alphaQ 54 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 54 i (c.val i) t) =
      ((jwv 54 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 54 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 54 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 54 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 54 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_55 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 55),
        qvalQ (fun t ↦ ∑ i, PE 55 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 55),
        (alphaQ 55 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 55 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 55 = 2 := by decide +kernel
  have hce : certE (55 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then 27 else if j.val = 1 then -7 else if j.val = 2 then -1 else -7)) := by decide +kernel
  have hs : (l2At (55 : Fin 1104)).2.2 = 14905029788 := by decide +kernel
  have hp : parent2 (55 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 55 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 55 c] :
    ∀ c ∈ Finset.univ, (alphaQ 55 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 55 i (c.val i) t) =
      ((jwv 55 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 55 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 55 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 55 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 55 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_56 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 56),
        qvalQ (fun t ↦ ∑ i, PE 56 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 56),
        (alphaQ 56 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 56 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 56 = 1 := by decide +kernel
  have hce : certE (56 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hs : (l2At (56 : Fin 1104)).2.2 = 21067775997 := by decide +kernel
  have hp : parent2 (56 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 56 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 56 c] :
    ∀ c ∈ Finset.univ, (alphaQ 56 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 56 i (c.val i) t) =
      ((jwv 56 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 56 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 56 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 56 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 56 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_57 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 57),
        qvalQ (fun t ↦ ∑ i, PE 57 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 57),
        (alphaQ 57 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 57 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 57 = 0 := by decide +kernel
  have hce : certE (57 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (57 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (57 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 57 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 57 c] :
    ∀ c ∈ Finset.univ, (alphaQ 57 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 57 i (c.val i) t) =
      ((jwv 57 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 57 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 57 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 57 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 57 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_58 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 58),
        qvalQ (fun t ↦ ∑ i, PE 58 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 58),
        (alphaQ 58 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 58 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 58 = 2 := by decide +kernel
  have hce : certE (58 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (58 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (58 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 58 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 58 c] :
    ∀ c ∈ Finset.univ, (alphaQ 58 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 58 i (c.val i) t) =
      ((jwv 58 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 58 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 58 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 58 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 58 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_59 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 59),
        qvalQ (fun t ↦ ∑ i, PE 59 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 59),
        (alphaQ 59 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 59 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 59 = 1 := by decide +kernel
  have hce : certE (59 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hs : (l2At (59 : Fin 1104)).2.2 = 20993285936 := by decide +kernel
  have hp : parent2 (59 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 59 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 59 c] :
    ∀ c ∈ Finset.univ, (alphaQ 59 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 59 i (c.val i) t) =
      ((jwv 59 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 59 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 59 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 59 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 59 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_60 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 60),
        qvalQ (fun t ↦ ∑ i, PE 60 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 60),
        (alphaQ 60 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 60 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 60 = 0 := by decide +kernel
  have hce : certE (60 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -13 else if j.val = 1 then 4 else if j.val = 2 then -2 else 2)) := by decide +kernel
  have hs : (l2At (60 : Fin 1104)).2.2 = 19381560954 := by decide +kernel
  have hp : parent2 (60 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 60 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 60 c] :
    ∀ c ∈ Finset.univ, (alphaQ 60 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 60 i (c.val i) t) =
      ((jwv 60 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 60 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 60 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 60 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 60 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_61 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 61),
        qvalQ (fun t ↦ ∑ i, PE 61 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 61),
        (alphaQ 61 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 61 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 61 = 2 := by decide +kernel
  have hce : certE (61 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 8 else if j.val = 1 then 7 else if j.val = 2 then -4 else -6)) := by decide +kernel
  have hs : (l2At (61 : Fin 1104)).2.2 = 7612993848 := by decide +kernel
  have hp : parent2 (61 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 61 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 61 c] :
    ∀ c ∈ Finset.univ, (alphaQ 61 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 61 i (c.val i) t) =
      ((jwv 61 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 61 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 61 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 61 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 61 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_62 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 62),
        qvalQ (fun t ↦ ∑ i, PE 62 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 62),
        (alphaQ 62 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 62 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 62 = 1 := by decide +kernel
  have hce : certE (62 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hs : (l2At (62 : Fin 1104)).2.2 = 20993286957 := by decide +kernel
  have hp : parent2 (62 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 62 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 62 c] :
    ∀ c ∈ Finset.univ, (alphaQ 62 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 62 i (c.val i) t) =
      ((jwv 62 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 62 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 62 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 62 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 62 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_63 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 63),
        qvalQ (fun t ↦ ∑ i, PE 63 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 63),
        (alphaQ 63 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 63 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 63 = 0 := by decide +kernel
  have hce : certE (63 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then 13 else if j.val = 1 then -8 else if j.val = 2 then 1 else -3)) := by decide +kernel
  have hs : (l2At (63 : Fin 1104)).2.2 = 18202107551 := by decide +kernel
  have hp : parent2 (63 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 63 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 63 c] :
    ∀ c ∈ Finset.univ, (alphaQ 63 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 63 i (c.val i) t) =
      ((jwv 63 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 63 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 63 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 63 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 63 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_64 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 64),
        qvalQ (fun t ↦ ∑ i, PE 64 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 64),
        (alphaQ 64 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 64 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 64 = 2 := by decide +kernel
  have hce : certE (64 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (64 : Fin 1104)).2.2 = 20923898598 := by decide +kernel
  have hp : parent2 (64 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 64 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 64 c] :
    ∀ c ∈ Finset.univ, (alphaQ 64 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 64 i (c.val i) t) =
      ((jwv 64 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 64 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 64 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 64 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 64 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_65 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 65),
        qvalQ (fun t ↦ ∑ i, PE 65 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 65),
        (alphaQ 65 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 65 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 65 = 1 := by decide +kernel
  have hce : certE (65 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (65 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (65 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 65 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 65 c] :
    ∀ c ∈ Finset.univ, (alphaQ 65 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 65 i (c.val i) t) =
      ((jwv 65 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 65 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 65 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 65 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 65 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_66 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 66),
        qvalQ (fun t ↦ ∑ i, PE 66 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 66),
        (alphaQ 66 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 66 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 66 = 0 := by decide +kernel
  have hce : certE (66 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -9 else if j.val = 1 then -2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hs : (l2At (66 : Fin 1104)).2.2 = 19375956243 := by decide +kernel
  have hp : parent2 (66 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 66 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 66 c] :
    ∀ c ∈ Finset.univ, (alphaQ 66 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 66 i (c.val i) t) =
      ((jwv 66 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 66 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 66 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 66 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 66 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_67 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 67),
        qvalQ (fun t ↦ ∑ i, PE 67 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 67),
        (alphaQ 67 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 67 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 67 = 2 := by decide +kernel
  have hce : certE (67 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (67 : Fin 1104)).2.2 = 20923897659 := by decide +kernel
  have hp : parent2 (67 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 67 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 67 c] :
    ∀ c ∈ Finset.univ, (alphaQ 67 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 67 i (c.val i) t) =
      ((jwv 67 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 67 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 67 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 67 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 67 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_68 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 68),
        qvalQ (fun t ↦ ∑ i, PE 68 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 68),
        (alphaQ 68 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 68 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 68 = 1 := by decide +kernel
  have hce : certE (68 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-10 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else 4) else (if j.val = 0 then -34 else if j.val = 1 then 5 else if j.val = 2 then 7 else 1)) := by decide +kernel
  have hs : (l2At (68 : Fin 1104)).2.2 = 7735247595 := by decide +kernel
  have hp : parent2 (68 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 68 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 68 c] :
    ∀ c ∈ Finset.univ, (alphaQ 68 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 68 i (c.val i) t) =
      ((jwv 68 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 68 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 68 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 68 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 68 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_69 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 69),
        qvalQ (fun t ↦ ∑ i, PE 69 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 69),
        (alphaQ 69 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 69 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 69 = 0 := by decide +kernel
  have hce : certE (69 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then -18 else if j.val = 1 then -2 else if j.val = 2 then 3 else 3)) := by decide +kernel
  have hs : (l2At (69 : Fin 1104)).2.2 = 18173971401 := by decide +kernel
  have hp : parent2 (69 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 69 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 69 c] :
    ∀ c ∈ Finset.univ, (alphaQ 69 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 69 i (c.val i) t) =
      ((jwv 69 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 69 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 69 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 69 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 69 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_70 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 70),
        qvalQ (fun t ↦ ∑ i, PE 70 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 70),
        (alphaQ 70 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 70 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 70 = 2 := by decide +kernel
  have hce : certE (70 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (70 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (70 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 70 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 70 c] :
    ∀ c ∈ Finset.univ, (alphaQ 70 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 70 i (c.val i) t) =
      ((jwv 70 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 70 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 70 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 70 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 70 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_71 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 71),
        qvalQ (fun t ↦ ∑ i, PE 71 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 71),
        (alphaQ 71 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 71 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 71 = 1 := by decide +kernel
  have hce : certE (71 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then -23 else if j.val = 1 then -1 else if j.val = 2 then 2 else 5)) := by decide +kernel
  have hs : (l2At (71 : Fin 1104)).2.2 = 16694913619 := by decide +kernel
  have hp : parent2 (71 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 71 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 71 c] :
    ∀ c ∈ Finset.univ, (alphaQ 71 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 71 i (c.val i) t) =
      ((jwv 71 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 71 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 71 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 71 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 71 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_72 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 72),
        qvalQ (fun t ↦ ∑ i, PE 72 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 72),
        (alphaQ 72 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 72 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 72 = 0 := by decide +kernel
  have hce : certE (72 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (72 : Fin 1104)).2.2 = 21076555263 := by decide +kernel
  have hp : parent2 (72 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 72 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 72 c] :
    ∀ c ∈ Finset.univ, (alphaQ 72 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 72 i (c.val i) t) =
      ((jwv 72 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 72 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 72 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 72 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 72 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_73 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 73),
        qvalQ (fun t ↦ ∑ i, PE 73 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 73),
        (alphaQ 73 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 73 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 73 = 2 := by decide +kernel
  have hce : certE (73 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hs : (l2At (73 : Fin 1104)).2.2 = 21067354254 := by decide +kernel
  have hp : parent2 (73 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 73 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 73 c] :
    ∀ c ∈ Finset.univ, (alphaQ 73 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 73 i (c.val i) t) =
      ((jwv 73 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 73 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 73 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 73 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 73 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_74 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 74),
        qvalQ (fun t ↦ ∑ i, PE 74 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 74),
        (alphaQ 74 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 74 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 74 = 1 := by decide +kernel
  have hce : certE (74 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then -1 else -2)) := by decide +kernel
  have hs : (l2At (74 : Fin 1104)).2.2 = 4081460277 := by decide +kernel
  have hp : parent2 (74 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 74 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 74 c] :
    ∀ c ∈ Finset.univ, (alphaQ 74 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 74 i (c.val i) t) =
      ((jwv 74 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 74 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 74 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 74 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 74 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_75 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 75),
        qvalQ (fun t ↦ ∑ i, PE 75 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 75),
        (alphaQ 75 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 75 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 75 = 0 := by decide +kernel
  have hce : certE (75 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (75 : Fin 1104)).2.2 = 21076559156 := by decide +kernel
  have hp : parent2 (75 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 75 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 75 c] :
    ∀ c ∈ Finset.univ, (alphaQ 75 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 75 i (c.val i) t) =
      ((jwv 75 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 75 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 75 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 75 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 75 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_76 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 76),
        qvalQ (fun t ↦ ∑ i, PE 76 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 76),
        (alphaQ 76 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 76 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 76 = 2 := by decide +kernel
  have hce : certE (76 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (76 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (76 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 76 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 76 c] :
    ∀ c ∈ Finset.univ, (alphaQ 76 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 76 i (c.val i) t) =
      ((jwv 76 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 76 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 76 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 76 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 76 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_77 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 77),
        qvalQ (fun t ↦ ∑ i, PE 77 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 77),
        (alphaQ 77 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 77 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 77 = 1 := by decide +kernel
  have hce : certE (77 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then 25 else if j.val = 1 then -4 else if j.val = 2 then -2 else -7)) := by decide +kernel
  have hs : (l2At (77 : Fin 1104)).2.2 = 20119347778 := by decide +kernel
  have hp : parent2 (77 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 77 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 77 c] :
    ∀ c ∈ Finset.univ, (alphaQ 77 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 77 i (c.val i) t) =
      ((jwv 77 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 77 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 77 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 77 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 77 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_78 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 78),
        qvalQ (fun t ↦ ∑ i, PE 78 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 78),
        (alphaQ 78 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 78 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 78 = 0 := by decide +kernel
  have hce : certE (78 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -27 else if j.val = 1 then -1 else if j.val = 2 then 0 else 2)) := by decide +kernel
  have hs : (l2At (78 : Fin 1104)).2.2 = 121689 := by decide +kernel
  have hp : parent2 (78 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 78 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 78 c] :
    ∀ c ∈ Finset.univ, (alphaQ 78 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 78 i (c.val i) t) =
      ((jwv 78 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 78 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 78 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 78 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 78 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_79 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 79),
        qvalQ (fun t ↦ ∑ i, PE 79 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 79),
        (alphaQ 79 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 79 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 79 = 2 := by decide +kernel
  have hce : certE (79 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 0 else 1)) := by decide +kernel
  have hs : (l2At (79 : Fin 1104)).2.2 = 117353 := by decide +kernel
  have hp : parent2 (79 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 79 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 79 c] :
    ∀ c ∈ Finset.univ, (alphaQ 79 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 79 i (c.val i) t) =
      ((jwv 79 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 79 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 79 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 79 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 79 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_80 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 80),
        qvalQ (fun t ↦ ∑ i, PE 80 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 80),
        (alphaQ 80 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 80 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 80 = 1 := by decide +kernel
  have hce : certE (80 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then 25 else if j.val = 1 then -4 else if j.val = 2 then -2 else -7)) := by decide +kernel
  have hs : (l2At (80 : Fin 1104)).2.2 = 20119347571 := by decide +kernel
  have hp : parent2 (80 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 80 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 80 c] :
    ∀ c ∈ Finset.univ, (alphaQ 80 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 80 i (c.val i) t) =
      ((jwv 80 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 80 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 80 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 80 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 80 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_81 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 81),
        qvalQ (fun t ↦ ∑ i, PE 81 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 81),
        (alphaQ 81 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 81 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 81 = 0 := by decide +kernel
  have hce : certE (81 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (81 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (81 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 81 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 81 c] :
    ∀ c ∈ Finset.univ, (alphaQ 81 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 81 i (c.val i) t) =
      ((jwv 81 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 81 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 81 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 81 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 81 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_82 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 82),
        qvalQ (fun t ↦ ∑ i, PE 82 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 82),
        (alphaQ 82 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 82 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 82 = 2 := by decide +kernel
  have hce : certE (82 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hs : (l2At (82 : Fin 1104)).2.2 = 21055268660 := by decide +kernel
  have hp : parent2 (82 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 82 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 82 c] :
    ∀ c ∈ Finset.univ, (alphaQ 82 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 82 i (c.val i) t) =
      ((jwv 82 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 82 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 82 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 82 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 82 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_83 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 83),
        qvalQ (fun t ↦ ∑ i, PE 83 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 83),
        (alphaQ 83 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 83 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 83 = 1 := by decide +kernel
  have hce : certE (83 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then -1 else -2)) := by decide +kernel
  have hs : (l2At (83 : Fin 1104)).2.2 = 4081280853 := by decide +kernel
  have hp : parent2 (83 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 83 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 83 c] :
    ∀ c ∈ Finset.univ, (alphaQ 83 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 83 i (c.val i) t) =
      ((jwv 83 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 83 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 83 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 83 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 83 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_84 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 84),
        qvalQ (fun t ↦ ∑ i, PE 84 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 84),
        (alphaQ 84 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 84 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 84 = 0 := by decide +kernel
  have hce : certE (84 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hs : (l2At (84 : Fin 1104)).2.2 = 21088731015 := by decide +kernel
  have hp : parent2 (84 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 84 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 84 c] :
    ∀ c ∈ Finset.univ, (alphaQ 84 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 84 i (c.val i) t) =
      ((jwv 84 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 84 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 84 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 84 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 84 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_85 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 85),
        qvalQ (fun t ↦ ∑ i, PE 85 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 85),
        (alphaQ 85 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 85 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 85 = 2 := by decide +kernel
  have hce : certE (85 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hs : (l2At (85 : Fin 1104)).2.2 = 21055260762 := by decide +kernel
  have hp : parent2 (85 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 85 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 85 c] :
    ∀ c ∈ Finset.univ, (alphaQ 85 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 85 i (c.val i) t) =
      ((jwv 85 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 85 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 85 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 85 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 85 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_86 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 86),
        qvalQ (fun t ↦ ∑ i, PE 86 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 86),
        (alphaQ 86 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 86 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 86 = 1 := by decide +kernel
  have hce : certE (86 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then -24 else if j.val = 1 then -8 else if j.val = 2 then 6 else 6)) := by decide +kernel
  have hs : (l2At (86 : Fin 1104)).2.2 = 16700500508 := by decide +kernel
  have hp : parent2 (86 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 86 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 86 c] :
    ∀ c ∈ Finset.univ, (alphaQ 86 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 86 i (c.val i) t) =
      ((jwv 86 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 86 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 86 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 86 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 86 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_87 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 87),
        qvalQ (fun t ↦ ∑ i, PE 87 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 87),
        (alphaQ 87 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 87 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 87 = 0 := by decide +kernel
  have hce : certE (87 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (87 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (87 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 87 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 87 c] :
    ∀ c ∈ Finset.univ, (alphaQ 87 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 87 i (c.val i) t) =
      ((jwv 87 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 87 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 87 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 87 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 87 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_88 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 88),
        qvalQ (fun t ↦ ∑ i, PE 88 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 88),
        (alphaQ 88 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 88 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 88 = 1 := by decide +kernel
  have hce : certE (88 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -26 else if j.val = 1 then 7 else if j.val = 2 then -1 else 0)) := by decide +kernel
  have hs : (l2At (88 : Fin 1104)).2.2 = 6517948 := by decide +kernel
  have hp : parent2 (88 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 88 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 88 c] :
    ∀ c ∈ Finset.univ, (alphaQ 88 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 88 i (c.val i) t) =
      ((jwv 88 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 88 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 88 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 88 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 88 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_89 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 89),
        qvalQ (fun t ↦ ∑ i, PE 89 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 89),
        (alphaQ 89 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 89 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 89 = 0 := by decide +kernel
  have hce : certE (89 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (89 : Fin 1104)).2.2 = 21076922202 := by decide +kernel
  have hp : parent2 (89 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 89 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 89 c] :
    ∀ c ∈ Finset.univ, (alphaQ 89 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 89 i (c.val i) t) =
      ((jwv 89 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 89 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 89 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 89 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 89 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_90 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 90),
        qvalQ (fun t ↦ ∑ i, PE 90 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 90),
        (alphaQ 90 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 90 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 90 = 1 := by decide +kernel
  have hce : certE (90 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (90 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (90 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 90 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 90 c] :
    ∀ c ∈ Finset.univ, (alphaQ 90 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 90 i (c.val i) t) =
      ((jwv 90 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 90 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 90 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 90 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 90 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_91 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 91),
        qvalQ (fun t ↦ ∑ i, PE 91 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 91),
        (alphaQ 91 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 91 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 91 = 0 := by decide +kernel
  have hce : certE (91 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (91 : Fin 1104)).2.2 = 21076726072 := by decide +kernel
  have hp : parent2 (91 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 91 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 91 c] :
    ∀ c ∈ Finset.univ, (alphaQ 91 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 91 i (c.val i) t) =
      ((jwv 91 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 91 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 91 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 91 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 91 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

end MME.L2Cert

theorem solution : ∀ j : Fin 46,
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨46 + j.val, by omega⟩),
        qvalQ (fun t ↦ ∑ i, PE ⟨46 + j.val, by omega⟩ i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨46 + j.val, by omega⟩),
        (alphaQ ⟨46 + j.val, by omega⟩ c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE ⟨46 + j.val, by omega⟩ i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.pcert_46
  | ⟨1, _⟩ => exact MME.L2Cert.pcert_47
  | ⟨2, _⟩ => exact MME.L2Cert.pcert_48
  | ⟨3, _⟩ => exact MME.L2Cert.pcert_49
  | ⟨4, _⟩ => exact MME.L2Cert.pcert_50
  | ⟨5, _⟩ => exact MME.L2Cert.pcert_51
  | ⟨6, _⟩ => exact MME.L2Cert.pcert_52
  | ⟨7, _⟩ => exact MME.L2Cert.pcert_53
  | ⟨8, _⟩ => exact MME.L2Cert.pcert_54
  | ⟨9, _⟩ => exact MME.L2Cert.pcert_55
  | ⟨10, _⟩ => exact MME.L2Cert.pcert_56
  | ⟨11, _⟩ => exact MME.L2Cert.pcert_57
  | ⟨12, _⟩ => exact MME.L2Cert.pcert_58
  | ⟨13, _⟩ => exact MME.L2Cert.pcert_59
  | ⟨14, _⟩ => exact MME.L2Cert.pcert_60
  | ⟨15, _⟩ => exact MME.L2Cert.pcert_61
  | ⟨16, _⟩ => exact MME.L2Cert.pcert_62
  | ⟨17, _⟩ => exact MME.L2Cert.pcert_63
  | ⟨18, _⟩ => exact MME.L2Cert.pcert_64
  | ⟨19, _⟩ => exact MME.L2Cert.pcert_65
  | ⟨20, _⟩ => exact MME.L2Cert.pcert_66
  | ⟨21, _⟩ => exact MME.L2Cert.pcert_67
  | ⟨22, _⟩ => exact MME.L2Cert.pcert_68
  | ⟨23, _⟩ => exact MME.L2Cert.pcert_69
  | ⟨24, _⟩ => exact MME.L2Cert.pcert_70
  | ⟨25, _⟩ => exact MME.L2Cert.pcert_71
  | ⟨26, _⟩ => exact MME.L2Cert.pcert_72
  | ⟨27, _⟩ => exact MME.L2Cert.pcert_73
  | ⟨28, _⟩ => exact MME.L2Cert.pcert_74
  | ⟨29, _⟩ => exact MME.L2Cert.pcert_75
  | ⟨30, _⟩ => exact MME.L2Cert.pcert_76
  | ⟨31, _⟩ => exact MME.L2Cert.pcert_77
  | ⟨32, _⟩ => exact MME.L2Cert.pcert_78
  | ⟨33, _⟩ => exact MME.L2Cert.pcert_79
  | ⟨34, _⟩ => exact MME.L2Cert.pcert_80
  | ⟨35, _⟩ => exact MME.L2Cert.pcert_81
  | ⟨36, _⟩ => exact MME.L2Cert.pcert_82
  | ⟨37, _⟩ => exact MME.L2Cert.pcert_83
  | ⟨38, _⟩ => exact MME.L2Cert.pcert_84
  | ⟨39, _⟩ => exact MME.L2Cert.pcert_85
  | ⟨40, _⟩ => exact MME.L2Cert.pcert_86
  | ⟨41, _⟩ => exact MME.L2Cert.pcert_87
  | ⟨42, _⟩ => exact MME.L2Cert.pcert_88
  | ⟨43, _⟩ => exact MME.L2Cert.pcert_89
  | ⟨44, _⟩ => exact MME.L2Cert.pcert_90
  | ⟨45, _⟩ => exact MME.L2Cert.pcert_91
  | ⟨n + 46, h⟩ => exact absurd h (by omega)
