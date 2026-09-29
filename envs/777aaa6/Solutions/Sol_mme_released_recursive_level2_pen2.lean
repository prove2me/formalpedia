-- Prove2me | solution 1 for mme_released_recursive_level2_pen2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T02:44:36.519885+00:00
-- url     : https://prove2.me/submissions/1d6cafee-9c22-4ae3-916d-3159185b04fd

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

theorem pcert_92 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 92),
        qvalQ (fun t ↦ ∑ i, PE 92 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 92),
        (alphaQ 92 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 92 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 92 = 1 := by decide +kernel
  have hce : certE (92 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -18 else if j.val = 1 then -5 else if j.val = 2 then -1 else 8)) := by decide +kernel
  have hs : (l2At (92 : Fin 1104)).2.2 = 18098765117 := by decide +kernel
  have hp : parent2 (92 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 92 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 92 c] :
    ∀ c ∈ Finset.univ, (alphaQ 92 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 92 i (c.val i) t) =
      ((jwv 92 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 92 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 92 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 92 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 92 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_93 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 93),
        qvalQ (fun t ↦ ∑ i, PE 93 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 93),
        (alphaQ 93 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 93 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 93 = 0 := by decide +kernel
  have hce : certE (93 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (93 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (93 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 93 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 93 c] :
    ∀ c ∈ Finset.univ, (alphaQ 93 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 93 i (c.val i) t) =
      ((jwv 93 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 93 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 93 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 93 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 93 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_94 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 94),
        qvalQ (fun t ↦ ∑ i, PE 94 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 94),
        (alphaQ 94 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 94 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 94 = 1 := by decide +kernel
  have hce : certE (94 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (94 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (94 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 94 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 94 c] :
    ∀ c ∈ Finset.univ, (alphaQ 94 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 94 i (c.val i) t) =
      ((jwv 94 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 94 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 94 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 94 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 94 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_95 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 95),
        qvalQ (fun t ↦ ∑ i, PE 95 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 95),
        (alphaQ 95 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 95 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 95 = 0 := by decide +kernel
  have hce : certE (95 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (95 : Fin 1104)).2.2 = 21076668434 := by decide +kernel
  have hp : parent2 (95 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 95 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 95 c] :
    ∀ c ∈ Finset.univ, (alphaQ 95 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 95 i (c.val i) t) =
      ((jwv 95 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 95 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 95 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 95 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 95 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_96 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 96),
        qvalQ (fun t ↦ ∑ i, PE 96 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 96),
        (alphaQ 96 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 96 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 96 = 1 := by decide +kernel
  have hce : certE (96 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -18 else if j.val = 1 then 6 else if j.val = 2 then 6 else -4)) := by decide +kernel
  have hs : (l2At (96 : Fin 1104)).2.2 = 18098224427 := by decide +kernel
  have hp : parent2 (96 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 96 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 96 c] :
    ∀ c ∈ Finset.univ, (alphaQ 96 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 96 i (c.val i) t) =
      ((jwv 96 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 96 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 96 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 96 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 96 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_97 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 97),
        qvalQ (fun t ↦ ∑ i, PE 97 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 97),
        (alphaQ 97 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 97 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 97 = 0 := by decide +kernel
  have hce : certE (97 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (97 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (97 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 97 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 97 c] :
    ∀ c ∈ Finset.univ, (alphaQ 97 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 97 i (c.val i) t) =
      ((jwv 97 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 97 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 97 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 97 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 97 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_98 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 98),
        qvalQ (fun t ↦ ∑ i, PE 98 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 98),
        (alphaQ 98 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 98 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 98 = 2 := by decide +kernel
  have hce : certE (98 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then 16 else if j.val = 1 then 1 else if j.val = 2 then -3 else -8)) := by decide +kernel
  have hs : (l2At (98 : Fin 1104)).2.2 = 272837776 := by decide +kernel
  have hp : parent2 (98 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 98 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 98 c] :
    ∀ c ∈ Finset.univ, (alphaQ 98 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 98 i (c.val i) t) =
      ((jwv 98 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 98 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 98 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 98 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 98 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_99 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 99),
        qvalQ (fun t ↦ ∑ i, PE 99 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 99),
        (alphaQ 99 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 99 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 99 = 0 := by decide +kernel
  have hce : certE (99 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (99 : Fin 1104)).2.2 = 21076532873 := by decide +kernel
  have hp : parent2 (99 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 99 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 99 c] :
    ∀ c ∈ Finset.univ, (alphaQ 99 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 99 i (c.val i) t) =
      ((jwv 99 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 99 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 99 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 99 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 99 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_100 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 100),
        qvalQ (fun t ↦ ∑ i, PE 100 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 100),
        (alphaQ 100 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 100 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 100 = 2 := by decide +kernel
  have hce : certE (100 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 9 else if j.val = 1 then -5 else if j.val = 2 then 1 else -5)) := by decide +kernel
  have hs : (l2At (100 : Fin 1104)).2.2 = 626819267 := by decide +kernel
  have hp : parent2 (100 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 100 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 100 c] :
    ∀ c ∈ Finset.univ, (alphaQ 100 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 100 i (c.val i) t) =
      ((jwv 100 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 100 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 100 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 100 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 100 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_101 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 101),
        qvalQ (fun t ↦ ∑ i, PE 101 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 101),
        (alphaQ 101 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 101 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 101 = 0 := by decide +kernel
  have hce : certE (101 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (101 : Fin 1104)).2.2 = 21076562650 := by decide +kernel
  have hp : parent2 (101 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 101 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 101 c] :
    ∀ c ∈ Finset.univ, (alphaQ 101 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 101 i (c.val i) t) =
      ((jwv 101 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 101 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 101 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 101 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 101 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_102 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 102),
        qvalQ (fun t ↦ ∑ i, PE 102 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 102),
        (alphaQ 102 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 102 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 102 = 2 := by decide +kernel
  have hce : certE (102 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -36 else if j.val = 1 then 7 else if j.val = 2 then 2 else 3)) := by decide +kernel
  have hs : (l2At (102 : Fin 1104)).2.2 = 272877465 := by decide +kernel
  have hp : parent2 (102 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 102 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 102 c] :
    ∀ c ∈ Finset.univ, (alphaQ 102 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 102 i (c.val i) t) =
      ((jwv 102 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 102 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 102 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 102 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 102 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_103 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 103),
        qvalQ (fun t ↦ ∑ i, PE 103 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 103),
        (alphaQ 103 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 103 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 103 = 0 := by decide +kernel
  have hce : certE (103 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (103 : Fin 1104)).2.2 = 21076559126 := by decide +kernel
  have hp : parent2 (103 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 103 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 103 c] :
    ∀ c ∈ Finset.univ, (alphaQ 103 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 103 i (c.val i) t) =
      ((jwv 103 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 103 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 103 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 103 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 103 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_104 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 104),
        qvalQ (fun t ↦ ∑ i, PE 104 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 104),
        (alphaQ 104 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 104 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 104 = 2 := by decide +kernel
  have hce : certE (104 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (104 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (104 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 104 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 104 c] :
    ∀ c ∈ Finset.univ, (alphaQ 104 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 104 i (c.val i) t) =
      ((jwv 104 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 104 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 104 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 104 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 104 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_105 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 105),
        qvalQ (fun t ↦ ∑ i, PE 105 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 105),
        (alphaQ 105 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 105 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 105 = 1 := by decide +kernel
  have hce : certE (105 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -4 else if j.val = 1 then -1 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hs : (l2At (105 : Fin 1104)).2.2 = 19369793621 := by decide +kernel
  have hp : parent2 (105 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 105 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 105 c] :
    ∀ c ∈ Finset.univ, (alphaQ 105 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 105 i (c.val i) t) =
      ((jwv 105 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 105 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 105 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 105 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 105 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_106 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 106),
        qvalQ (fun t ↦ ∑ i, PE 106 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 106),
        (alphaQ 106 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 106 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 106 = 0 := by decide +kernel
  have hce : certE (106 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (106 : Fin 1104)).2.2 = 21076560445 := by decide +kernel
  have hp : parent2 (106 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 106 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 106 c] :
    ∀ c ∈ Finset.univ, (alphaQ 106 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 106 i (c.val i) t) =
      ((jwv 106 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 106 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 106 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 106 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 106 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_107 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 107),
        qvalQ (fun t ↦ ∑ i, PE 107 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 107),
        (alphaQ 107 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 107 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 107 = 2 := by decide +kernel
  have hce : certE (107 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 7 else if j.val = 1 then -3 else if j.val = 2 then -4 else 0)) := by decide +kernel
  have hs : (l2At (107 : Fin 1104)).2.2 = 7584962385 := by decide +kernel
  have hp : parent2 (107 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 107 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 107 c] :
    ∀ c ∈ Finset.univ, (alphaQ 107 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 107 i (c.val i) t) =
      ((jwv 107 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 107 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 107 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 107 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 107 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_108 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 108),
        qvalQ (fun t ↦ ∑ i, PE 108 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 108),
        (alphaQ 108 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 108 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 108 = 1 := by decide +kernel
  have hce : certE (108 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -28 else if j.val = 1 then 7 else if j.val = 2 then 6 else -1)) := by decide +kernel
  have hs : (l2At (108 : Fin 1104)).2.2 = 18184590222 := by decide +kernel
  have hp : parent2 (108 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 108 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 108 c] :
    ∀ c ∈ Finset.univ, (alphaQ 108 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 108 i (c.val i) t) =
      ((jwv 108 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 108 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 108 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 108 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 108 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_109 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 109),
        qvalQ (fun t ↦ ∑ i, PE 109 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 109),
        (alphaQ 109 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 109 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 109 = 0 := by decide +kernel
  have hce : certE (109 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (109 : Fin 1104)).2.2 = 21076560243 := by decide +kernel
  have hp : parent2 (109 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 109 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 109 c] :
    ∀ c ∈ Finset.univ, (alphaQ 109 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 109 i (c.val i) t) =
      ((jwv 109 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 109 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 109 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 109 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 109 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_110 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 110),
        qvalQ (fun t ↦ ∑ i, PE 110 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 110),
        (alphaQ 110 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 110 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 110 = 2 := by decide +kernel
  have hce : certE (110 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (110 : Fin 1104)).2.2 = 20923898199 := by decide +kernel
  have hp : parent2 (110 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 110 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 110 c] :
    ∀ c ∈ Finset.univ, (alphaQ 110 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 110 i (c.val i) t) =
      ((jwv 110 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 110 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 110 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 110 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 110 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_111 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 111),
        qvalQ (fun t ↦ ∑ i, PE 111 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 111),
        (alphaQ 111 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 111 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 111 = 1 := by decide +kernel
  have hce : certE (111 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then -33 else if j.val = 1 then 3 else if j.val = 2 then 0 else 8)) := by decide +kernel
  have hs : (l2At (111 : Fin 1104)).2.2 = 18121129290 := by decide +kernel
  have hp : parent2 (111 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 111 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 111 c] :
    ∀ c ∈ Finset.univ, (alphaQ 111 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 111 i (c.val i) t) =
      ((jwv 111 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 111 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 111 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 111 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 111 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_112 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 112),
        qvalQ (fun t ↦ ∑ i, PE 112 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 112),
        (alphaQ 112 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 112 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 112 = 0 := by decide +kernel
  have hce : certE (112 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -8 else if j.val = 1 then -4 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (112 : Fin 1104)).2.2 = 7846036071 := by decide +kernel
  have hp : parent2 (112 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 112 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 112 c] :
    ∀ c ∈ Finset.univ, (alphaQ 112 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 112 i (c.val i) t) =
      ((jwv 112 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 112 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 112 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 112 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 112 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_113 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 113),
        qvalQ (fun t ↦ ∑ i, PE 113 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 113),
        (alphaQ 113 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 113 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 113 = 2 := by decide +kernel
  have hce : certE (113 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (113 : Fin 1104)).2.2 = 20923899337 := by decide +kernel
  have hp : parent2 (113 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 113 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 113 c] :
    ∀ c ∈ Finset.univ, (alphaQ 113 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 113 i (c.val i) t) =
      ((jwv 113 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 113 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 113 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 113 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 113 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_114 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 114),
        qvalQ (fun t ↦ ∑ i, PE 114 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 114),
        (alphaQ 114 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 114 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 114 = 1 := by decide +kernel
  have hce : certE (114 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 3 else if j.val = 1 then 3 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hs : (l2At (114 : Fin 1104)).2.2 = 19353430759 := by decide +kernel
  have hp : parent2 (114 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 114 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 114 c] :
    ∀ c ∈ Finset.univ, (alphaQ 114 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 114 i (c.val i) t) =
      ((jwv 114 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 114 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 114 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 114 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 114 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_115 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 115),
        qvalQ (fun t ↦ ∑ i, PE 115 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 115),
        (alphaQ 115 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 115 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 115 = 0 := by decide +kernel
  have hce : certE (115 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (115 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (115 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 115 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 115 c] :
    ∀ c ∈ Finset.univ, (alphaQ 115 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 115 i (c.val i) t) =
      ((jwv 115 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 115 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 115 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 115 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 115 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_116 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 116),
        qvalQ (fun t ↦ ∑ i, PE 116 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 116),
        (alphaQ 116 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 116 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 116 = 2 := by decide +kernel
  have hce : certE (116 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 7 else if j.val = 1 then -8 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hs : (l2At (116 : Fin 1104)).2.2 = 18138373679 := by decide +kernel
  have hp : parent2 (116 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 116 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 116 c] :
    ∀ c ∈ Finset.univ, (alphaQ 116 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 116 i (c.val i) t) =
      ((jwv 116 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 116 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 116 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 116 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 116 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_117 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 117),
        qvalQ (fun t ↦ ∑ i, PE 117 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 117),
        (alphaQ 117 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 117 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 117 = 1 := by decide +kernel
  have hce : certE (117 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then -5 else if j.val = 2 then 4 else 2) else (if j.val = 0 then -30 else if j.val = 1 then -7 else if j.val = 2 then 5 else 8)) := by decide +kernel
  have hs : (l2At (117 : Fin 1104)).2.2 = 7671998046 := by decide +kernel
  have hp : parent2 (117 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 117 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 117 c] :
    ∀ c ∈ Finset.univ, (alphaQ 117 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 117 i (c.val i) t) =
      ((jwv 117 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 117 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 117 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 117 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 117 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_118 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 118),
        qvalQ (fun t ↦ ∑ i, PE 118 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 118),
        (alphaQ 118 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 118 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 118 = 0 := by decide +kernel
  have hce : certE (118 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (118 : Fin 1104)).2.2 = 21076560635 := by decide +kernel
  have hp : parent2 (118 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 118 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 118 c] :
    ∀ c ∈ Finset.univ, (alphaQ 118 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 118 i (c.val i) t) =
      ((jwv 118 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 118 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 118 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 118 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 118 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_119 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 119),
        qvalQ (fun t ↦ ∑ i, PE 119 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 119),
        (alphaQ 119 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 119 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 119 = 2 := by decide +kernel
  have hce : certE (119 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then -40 else if j.val = 1 then 4 else if j.val = 2 then 6 else 5)) := by decide +kernel
  have hs : (l2At (119 : Fin 1104)).2.2 = 19346629376 := by decide +kernel
  have hp : parent2 (119 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 119 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 119 c] :
    ∀ c ∈ Finset.univ, (alphaQ 119 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 119 i (c.val i) t) =
      ((jwv 119 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 119 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 119 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 119 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 119 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_120 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 120),
        qvalQ (fun t ↦ ∑ i, PE 120 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 120),
        (alphaQ 120 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 120 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 120 = 1 := by decide +kernel
  have hce : certE (120 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (120 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (120 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 120 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 120 c] :
    ∀ c ∈ Finset.univ, (alphaQ 120 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 120 i (c.val i) t) =
      ((jwv 120 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 120 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 120 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 120 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 120 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_121 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 121),
        qvalQ (fun t ↦ ∑ i, PE 121 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 121),
        (alphaQ 121 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 121 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 121 = 0 := by decide +kernel
  have hce : certE (121 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (121 : Fin 1104)).2.2 = 21076560992 := by decide +kernel
  have hp : parent2 (121 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 121 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 121 c] :
    ∀ c ∈ Finset.univ, (alphaQ 121 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 121 i (c.val i) t) =
      ((jwv 121 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 121 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 121 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 121 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 121 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_122 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 122),
        qvalQ (fun t ↦ ∑ i, PE 122 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 122),
        (alphaQ 122 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 122 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 122 = 2 := by decide +kernel
  have hce : certE (122 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 25 else if j.val = 1 then 5 else if j.val = 2 then -7 else -8)) := by decide +kernel
  have hs : (l2At (122 : Fin 1104)).2.2 = 18103299789 := by decide +kernel
  have hp : parent2 (122 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 122 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 122 c] :
    ∀ c ∈ Finset.univ, (alphaQ 122 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 122 i (c.val i) t) =
      ((jwv 122 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 122 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 122 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 122 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 122 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_123 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 123),
        qvalQ (fun t ↦ ∑ i, PE 123 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 123),
        (alphaQ 123 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 123 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 123 = 1 := by decide +kernel
  have hce : certE (123 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hs : (l2At (123 : Fin 1104)).2.2 = 20993285071 := by decide +kernel
  have hp : parent2 (123 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 123 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 123 c] :
    ∀ c ∈ Finset.univ, (alphaQ 123 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 123 i (c.val i) t) =
      ((jwv 123 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 123 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 123 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 123 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 123 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_124 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 124),
        qvalQ (fun t ↦ ∑ i, PE 124 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 124),
        (alphaQ 124 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 124 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 124 = 0 := by decide +kernel
  have hce : certE (124 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -54 else if j.val = 1 then 7 else if j.val = 2 then 7 else 7)) := by decide +kernel
  have hs : (l2At (124 : Fin 1104)).2.2 = 7810925836 := by decide +kernel
  have hp : parent2 (124 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 124 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 124 c] :
    ∀ c ∈ Finset.univ, (alphaQ 124 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 124 i (c.val i) t) =
      ((jwv 124 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 124 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 124 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 124 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 124 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_125 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 125),
        qvalQ (fun t ↦ ∑ i, PE 125 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 125),
        (alphaQ 125 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 125 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 125 = 2 := by decide +kernel
  have hce : certE (125 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 13 else if j.val = 1 then 5 else if j.val = 2 then -3 else -7)) := by decide +kernel
  have hs : (l2At (125 : Fin 1104)).2.2 = 19335877605 := by decide +kernel
  have hp : parent2 (125 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 125 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 125 c] :
    ∀ c ∈ Finset.univ, (alphaQ 125 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 125 i (c.val i) t) =
      ((jwv 125 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 125 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 125 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 125 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 125 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_126 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 126),
        qvalQ (fun t ↦ ∑ i, PE 126 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 126),
        (alphaQ 126 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 126 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 126 = 1 := by decide +kernel
  have hce : certE (126 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hs : (l2At (126 : Fin 1104)).2.2 = 20993283444 := by decide +kernel
  have hp : parent2 (126 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 126 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 126 c] :
    ∀ c ∈ Finset.univ, (alphaQ 126 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 126 i (c.val i) t) =
      ((jwv 126 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 126 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 126 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 126 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 126 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_127 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 127),
        qvalQ (fun t ↦ ∑ i, PE 127 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 127),
        (alphaQ 127 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 127 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 127 = 0 := by decide +kernel
  have hce : certE (127 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (127 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (127 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 127 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 127 c] :
    ∀ c ∈ Finset.univ, (alphaQ 127 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 127 i (c.val i) t) =
      ((jwv 127 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 127 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 127 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 127 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 127 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_128 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 128),
        qvalQ (fun t ↦ ∑ i, PE 128 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 128),
        (alphaQ 128 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 128 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 128 = 1 := by decide +kernel
  have hce : certE (128 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -35 else if j.val = 1 then 6 else if j.val = 2 then 8 else -1)) := by decide +kernel
  have hs : (l2At (128 : Fin 1104)).2.2 = 1183861648 := by decide +kernel
  have hp : parent2 (128 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 128 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 128 c] :
    ∀ c ∈ Finset.univ, (alphaQ 128 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 128 i (c.val i) t) =
      ((jwv 128 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 128 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 128 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 128 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 128 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_129 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 129),
        qvalQ (fun t ↦ ∑ i, PE 129 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 129),
        (alphaQ 129 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 129 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 129 = 0 := by decide +kernel
  have hce : certE (129 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (129 : Fin 1104)).2.2 = 21076562508 := by decide +kernel
  have hp : parent2 (129 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 129 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 129 c] :
    ∀ c ∈ Finset.univ, (alphaQ 129 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 129 i (c.val i) t) =
      ((jwv 129 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 129 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 129 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 129 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 129 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_130 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 130),
        qvalQ (fun t ↦ ∑ i, PE 130 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 130),
        (alphaQ 130 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 130 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 130 = 1 := by decide +kernel
  have hce : certE (130 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -17 else if j.val = 1 then 4 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (130 : Fin 1104)).2.2 = 617967745 := by decide +kernel
  have hp : parent2 (130 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 130 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 130 c] :
    ∀ c ∈ Finset.univ, (alphaQ 130 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 130 i (c.val i) t) =
      ((jwv 130 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 130 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 130 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 130 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 130 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_131 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 131),
        qvalQ (fun t ↦ ∑ i, PE 131 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 131),
        (alphaQ 131 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 131 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 131 = 0 := by decide +kernel
  have hce : certE (131 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (131 : Fin 1104)).2.2 = 21076555753 := by decide +kernel
  have hp : parent2 (131 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 131 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 131 c] :
    ∀ c ∈ Finset.univ, (alphaQ 131 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 131 i (c.val i) t) =
      ((jwv 131 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 131 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 131 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 131 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 131 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_132 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 132),
        qvalQ (fun t ↦ ∑ i, PE 132 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 132),
        (alphaQ 132 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 132 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 132 = 1 := by decide +kernel
  have hce : certE (132 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -17 else if j.val = 1 then 4 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (132 : Fin 1104)).2.2 = 618028698 := by decide +kernel
  have hp : parent2 (132 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 132 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 132 c] :
    ∀ c ∈ Finset.univ, (alphaQ 132 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 132 i (c.val i) t) =
      ((jwv 132 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 132 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 132 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 132 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 132 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_133 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 133),
        qvalQ (fun t ↦ ∑ i, PE 133 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 133),
        (alphaQ 133 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 133 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 133 = 0 := by decide +kernel
  have hce : certE (133 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (133 : Fin 1104)).2.2 = 21076560635 := by decide +kernel
  have hp : parent2 (133 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 133 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 133 c] :
    ∀ c ∈ Finset.univ, (alphaQ 133 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 133 i (c.val i) t) =
      ((jwv 133 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 133 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 133 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 133 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 133 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_134 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 134),
        qvalQ (fun t ↦ ∑ i, PE 134 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 134),
        (alphaQ 134 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 134 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 134 = 2 := by decide +kernel
  have hce : certE (134 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (134 : Fin 1104)).2.2 = 20923915238 := by decide +kernel
  have hp : parent2 (134 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 134 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 134 c] :
    ∀ c ∈ Finset.univ, (alphaQ 134 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 134 i (c.val i) t) =
      ((jwv 134 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 134 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 134 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 134 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 134 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_135 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 135),
        qvalQ (fun t ↦ ∑ i, PE 135 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 135),
        (alphaQ 135 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 135 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 135 = 0 := by decide +kernel
  have hce : certE (135 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then -3 else 3)) := by decide +kernel
  have hs : (l2At (135 : Fin 1104)).2.2 = 1004889316 := by decide +kernel
  have hp : parent2 (135 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 135 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 135 c] :
    ∀ c ∈ Finset.univ, (alphaQ 135 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 135 i (c.val i) t) =
      ((jwv 135 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 135 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 135 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 135 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 135 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_136 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 136),
        qvalQ (fun t ↦ ∑ i, PE 136 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 136),
        (alphaQ 136 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 136 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 136 = 2 := by decide +kernel
  have hce : certE (136 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (136 : Fin 1104)).2.2 = 20923905429 := by decide +kernel
  have hp : parent2 (136 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 136 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 136 c] :
    ∀ c ∈ Finset.univ, (alphaQ 136 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 136 i (c.val i) t) =
      ((jwv 136 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 136 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 136 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 136 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 136 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_137 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 137),
        qvalQ (fun t ↦ ∑ i, PE 137 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 137),
        (alphaQ 137 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 137 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 137 = 0 := by decide +kernel
  have hce : certE (137 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -11 else if j.val = 1 then -3 else if j.val = 2 then -2 else 4)) := by decide +kernel
  have hs : (l2At (137 : Fin 1104)).2.2 = 1736885894 := by decide +kernel
  have hp : parent2 (137 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 137 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 137 c] :
    ∀ c ∈ Finset.univ, (alphaQ 137 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 137 i (c.val i) t) =
      ((jwv 137 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 137 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 137 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 137 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 137 i (a i) t)),
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
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨92 + j.val, by omega⟩),
        qvalQ (fun t ↦ ∑ i, PE ⟨92 + j.val, by omega⟩ i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨92 + j.val, by omega⟩),
        (alphaQ ⟨92 + j.val, by omega⟩ c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE ⟨92 + j.val, by omega⟩ i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.pcert_92
  | ⟨1, _⟩ => exact MME.L2Cert.pcert_93
  | ⟨2, _⟩ => exact MME.L2Cert.pcert_94
  | ⟨3, _⟩ => exact MME.L2Cert.pcert_95
  | ⟨4, _⟩ => exact MME.L2Cert.pcert_96
  | ⟨5, _⟩ => exact MME.L2Cert.pcert_97
  | ⟨6, _⟩ => exact MME.L2Cert.pcert_98
  | ⟨7, _⟩ => exact MME.L2Cert.pcert_99
  | ⟨8, _⟩ => exact MME.L2Cert.pcert_100
  | ⟨9, _⟩ => exact MME.L2Cert.pcert_101
  | ⟨10, _⟩ => exact MME.L2Cert.pcert_102
  | ⟨11, _⟩ => exact MME.L2Cert.pcert_103
  | ⟨12, _⟩ => exact MME.L2Cert.pcert_104
  | ⟨13, _⟩ => exact MME.L2Cert.pcert_105
  | ⟨14, _⟩ => exact MME.L2Cert.pcert_106
  | ⟨15, _⟩ => exact MME.L2Cert.pcert_107
  | ⟨16, _⟩ => exact MME.L2Cert.pcert_108
  | ⟨17, _⟩ => exact MME.L2Cert.pcert_109
  | ⟨18, _⟩ => exact MME.L2Cert.pcert_110
  | ⟨19, _⟩ => exact MME.L2Cert.pcert_111
  | ⟨20, _⟩ => exact MME.L2Cert.pcert_112
  | ⟨21, _⟩ => exact MME.L2Cert.pcert_113
  | ⟨22, _⟩ => exact MME.L2Cert.pcert_114
  | ⟨23, _⟩ => exact MME.L2Cert.pcert_115
  | ⟨24, _⟩ => exact MME.L2Cert.pcert_116
  | ⟨25, _⟩ => exact MME.L2Cert.pcert_117
  | ⟨26, _⟩ => exact MME.L2Cert.pcert_118
  | ⟨27, _⟩ => exact MME.L2Cert.pcert_119
  | ⟨28, _⟩ => exact MME.L2Cert.pcert_120
  | ⟨29, _⟩ => exact MME.L2Cert.pcert_121
  | ⟨30, _⟩ => exact MME.L2Cert.pcert_122
  | ⟨31, _⟩ => exact MME.L2Cert.pcert_123
  | ⟨32, _⟩ => exact MME.L2Cert.pcert_124
  | ⟨33, _⟩ => exact MME.L2Cert.pcert_125
  | ⟨34, _⟩ => exact MME.L2Cert.pcert_126
  | ⟨35, _⟩ => exact MME.L2Cert.pcert_127
  | ⟨36, _⟩ => exact MME.L2Cert.pcert_128
  | ⟨37, _⟩ => exact MME.L2Cert.pcert_129
  | ⟨38, _⟩ => exact MME.L2Cert.pcert_130
  | ⟨39, _⟩ => exact MME.L2Cert.pcert_131
  | ⟨40, _⟩ => exact MME.L2Cert.pcert_132
  | ⟨41, _⟩ => exact MME.L2Cert.pcert_133
  | ⟨42, _⟩ => exact MME.L2Cert.pcert_134
  | ⟨43, _⟩ => exact MME.L2Cert.pcert_135
  | ⟨44, _⟩ => exact MME.L2Cert.pcert_136
  | ⟨45, _⟩ => exact MME.L2Cert.pcert_137
  | ⟨n + 46, h⟩ => exact absurd h (by omega)
