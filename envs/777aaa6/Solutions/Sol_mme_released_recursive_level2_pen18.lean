-- Prove2me | solution 1 for mme_released_recursive_level2_pen18
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:31:56.366719+00:00
-- url     : https://prove2.me/submissions/47c1a363-d11c-4f2d-8be4-d661faef79aa

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

theorem pcert_828 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 828),
        qvalQ (fun t ↦ ∑ i, PE 828 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 828),
        (alphaQ 828 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 828 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 828 = 2 := by decide +kernel
  have hce : certE (828 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 8 else if j.val = 1 then 6 else if j.val = 2 then -7 else -4)) := by decide +kernel
  have hs : (l2At (828 : Fin 1104)).2.2 = 994835597 := by decide +kernel
  have hp : parent2 (828 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 828 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 828 c] :
    ∀ c ∈ Finset.univ, (alphaQ 828 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 828 i (c.val i) t) =
      ((jwv 828 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 828 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 828 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 828 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 828 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_829 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 829),
        qvalQ (fun t ↦ ∑ i, PE 829 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 829),
        (alphaQ 829 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 829 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 829 = 0 := by decide +kernel
  have hce : certE (829 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (829 : Fin 1104)).2.2 = 20992843062 := by decide +kernel
  have hp : parent2 (829 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 829 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 829 c] :
    ∀ c ∈ Finset.univ, (alphaQ 829 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 829 i (c.val i) t) =
      ((jwv 829 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 829 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 829 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 829 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 829 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_830 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 830),
        qvalQ (fun t ↦ ∑ i, PE 830 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 830),
        (alphaQ 830 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 830 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 830 = 2 := by decide +kernel
  have hce : certE (830 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -7 else if j.val = 1 then -4 else if j.val = 2 then 3 else -1)) := by decide +kernel
  have hs : (l2At (830 : Fin 1104)).2.2 = 1722361693 := by decide +kernel
  have hp : parent2 (830 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 830 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 830 c] :
    ∀ c ∈ Finset.univ, (alphaQ 830 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 830 i (c.val i) t) =
      ((jwv 830 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 830 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 830 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 830 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 830 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_831 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 831),
        qvalQ (fun t ↦ ∑ i, PE 831 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 831),
        (alphaQ 831 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 831 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 831 = 0 := by decide +kernel
  have hce : certE (831 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (831 : Fin 1104)).2.2 = 20992843641 := by decide +kernel
  have hp : parent2 (831 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 831 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 831 c] :
    ∀ c ∈ Finset.univ, (alphaQ 831 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 831 i (c.val i) t) =
      ((jwv 831 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 831 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 831 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 831 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 831 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_832 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 832),
        qvalQ (fun t ↦ ∑ i, PE 832 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 832),
        (alphaQ 832 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 832 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 832 = 2 := by decide +kernel
  have hce : certE (832 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 8 else if j.val = 1 then 6 else if j.val = 2 then -7 else -4)) := by decide +kernel
  have hs : (l2At (832 : Fin 1104)).2.2 = 994867062 := by decide +kernel
  have hp : parent2 (832 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 832 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 832 c] :
    ∀ c ∈ Finset.univ, (alphaQ 832 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 832 i (c.val i) t) =
      ((jwv 832 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 832 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 832 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 832 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 832 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_833 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 833),
        qvalQ (fun t ↦ ∑ i, PE 833 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 833),
        (alphaQ 833 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 833 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 833 = 0 := by decide +kernel
  have hce : certE (833 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (833 : Fin 1104)).2.2 = 20992843784 := by decide +kernel
  have hp : parent2 (833 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 833 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 833 c] :
    ∀ c ∈ Finset.univ, (alphaQ 833 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 833 i (c.val i) t) =
      ((jwv 833 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 833 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 833 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 833 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 833 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_834 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 834),
        qvalQ (fun t ↦ ∑ i, PE 834 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 834),
        (alphaQ 834 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 834 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 834 = 2 := by decide +kernel
  have hce : certE (834 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (834 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (834 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 834 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 834 c] :
    ∀ c ∈ Finset.univ, (alphaQ 834 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 834 i (c.val i) t) =
      ((jwv 834 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 834 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 834 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 834 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 834 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_835 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 835),
        qvalQ (fun t ↦ ∑ i, PE 835 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 835),
        (alphaQ 835 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 835 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 835 = 1 := by decide +kernel
  have hce : certE (835 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 18 else if j.val = 1 then -5 else if j.val = 2 then -8 else 1)) := by decide +kernel
  have hs : (l2At (835 : Fin 1104)).2.2 = 19334555441 := by decide +kernel
  have hp : parent2 (835 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 835 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 835 c] :
    ∀ c ∈ Finset.univ, (alphaQ 835 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 835 i (c.val i) t) =
      ((jwv 835 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 835 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 835 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 835 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 835 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_836 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 836),
        qvalQ (fun t ↦ ∑ i, PE 836 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 836),
        (alphaQ 836 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 836 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 836 = 0 := by decide +kernel
  have hce : certE (836 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (836 : Fin 1104)).2.2 = 20992843073 := by decide +kernel
  have hp : parent2 (836 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 836 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 836 c] :
    ∀ c ∈ Finset.univ, (alphaQ 836 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 836 i (c.val i) t) =
      ((jwv 836 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 836 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 836 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 836 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 836 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_837 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 837),
        qvalQ (fun t ↦ ∑ i, PE 837 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 837),
        (alphaQ 837 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 837 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 837 = 2 := by decide +kernel
  have hce : certE (837 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -6 else if j.val = 1 then 7 else if j.val = 2 then -4 else -1)) := by decide +kernel
  have hs : (l2At (837 : Fin 1104)).2.2 = 7810335879 := by decide +kernel
  have hp : parent2 (837 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 837 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 837 c] :
    ∀ c ∈ Finset.univ, (alphaQ 837 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 837 i (c.val i) t) =
      ((jwv 837 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 837 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 837 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 837 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 837 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_838 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 838),
        qvalQ (fun t ↦ ∑ i, PE 838 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 838),
        (alphaQ 838 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 838 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 838 = 1 := by decide +kernel
  have hce : certE (838 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then 25 else if j.val = 1 then 5 else if j.val = 2 then -7 else -8)) := by decide +kernel
  have hs : (l2At (838 : Fin 1104)).2.2 = 18102738739 := by decide +kernel
  have hp : parent2 (838 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 838 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 838 c] :
    ∀ c ∈ Finset.univ, (alphaQ 838 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 838 i (c.val i) t) =
      ((jwv 838 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 838 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 838 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 838 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 838 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_839 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 839),
        qvalQ (fun t ↦ ∑ i, PE 839 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 839),
        (alphaQ 839 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 839 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 839 = 0 := by decide +kernel
  have hce : certE (839 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (839 : Fin 1104)).2.2 = 20992842378 := by decide +kernel
  have hp : parent2 (839 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 839 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 839 c] :
    ∀ c ∈ Finset.univ, (alphaQ 839 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 839 i (c.val i) t) =
      ((jwv 839 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 839 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 839 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 839 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 839 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_840 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 840),
        qvalQ (fun t ↦ ∑ i, PE 840 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 840),
        (alphaQ 840 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 840 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 840 = 2 := by decide +kernel
  have hce : certE (840 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (840 : Fin 1104)).2.2 = 21076753645 := by decide +kernel
  have hp : parent2 (840 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 840 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 840 c] :
    ∀ c ∈ Finset.univ, (alphaQ 840 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 840 i (c.val i) t) =
      ((jwv 840 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 840 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 840 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 840 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 840 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_841 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 841),
        qvalQ (fun t ↦ ∑ i, PE 841 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 841),
        (alphaQ 841 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 841 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 841 = 1 := by decide +kernel
  have hce : certE (841 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 7 else if j.val = 1 then -8 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hs : (l2At (841 : Fin 1104)).2.2 = 18137828786 := by decide +kernel
  have hp : parent2 (841 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 841 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 841 c] :
    ∀ c ∈ Finset.univ, (alphaQ 841 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 841 i (c.val i) t) =
      ((jwv 841 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 841 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 841 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 841 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 841 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_842 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 842),
        qvalQ (fun t ↦ ∑ i, PE 842 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 842),
        (alphaQ 842 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 842 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 842 = 0 := by decide +kernel
  have hce : certE (842 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then -5 else if j.val = 2 then 4 else 2) else (if j.val = 0 then -29 else if j.val = 1 then 0 else if j.val = 2 then 1 else 7)) := by decide +kernel
  have hs : (l2At (842 : Fin 1104)).2.2 = 7669541458 := by decide +kernel
  have hp : parent2 (842 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 842 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 842 c] :
    ∀ c ∈ Finset.univ, (alphaQ 842 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 842 i (c.val i) t) =
      ((jwv 842 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 842 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 842 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 842 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 842 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_843 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 843),
        qvalQ (fun t ↦ ∑ i, PE 843 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 843),
        (alphaQ 843 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 843 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 843 = 2 := by decide +kernel
  have hce : certE (843 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (843 : Fin 1104)).2.2 = 21076754060 := by decide +kernel
  have hp : parent2 (843 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 843 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 843 c] :
    ∀ c ∈ Finset.univ, (alphaQ 843 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 843 i (c.val i) t) =
      ((jwv 843 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 843 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 843 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 843 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 843 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_844 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 844),
        qvalQ (fun t ↦ ∑ i, PE 844 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 844),
        (alphaQ 844 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 844 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 844 = 1 := by decide +kernel
  have hce : certE (844 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then -5 else -3)) := by decide +kernel
  have hs : (l2At (844 : Fin 1104)).2.2 = 19345454410 := by decide +kernel
  have hp : parent2 (844 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 844 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 844 c] :
    ∀ c ∈ Finset.univ, (alphaQ 844 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 844 i (c.val i) t) =
      ((jwv 844 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 844 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 844 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 844 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 844 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_845 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 845),
        qvalQ (fun t ↦ ∑ i, PE 845 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 845),
        (alphaQ 845 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 845 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 845 = 0 := by decide +kernel
  have hce : certE (845 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (845 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (845 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 845 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 845 c] :
    ∀ c ∈ Finset.univ, (alphaQ 845 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 845 i (c.val i) t) =
      ((jwv 845 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 845 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 845 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 845 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 845 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_846 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 846),
        qvalQ (fun t ↦ ∑ i, PE 846 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 846),
        (alphaQ 846 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 846 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 846 = 2 := by decide +kernel
  have hce : certE (846 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then 9 else if j.val = 1 then -2 else if j.val = 2 then -5 else 0)) := by decide +kernel
  have hs : (l2At (846 : Fin 1104)).2.2 = 18202765233 := by decide +kernel
  have hp : parent2 (846 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 846 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 846 c] :
    ∀ c ∈ Finset.univ, (alphaQ 846 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 846 i (c.val i) t) =
      ((jwv 846 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 846 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 846 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 846 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 846 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_847 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 847),
        qvalQ (fun t ↦ ∑ i, PE 847 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 847),
        (alphaQ 847 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 847 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 847 = 1 := by decide +kernel
  have hce : certE (847 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 8 else if j.val = 1 then 7 else if j.val = 2 then -4 else -6)) := by decide +kernel
  have hs : (l2At (847 : Fin 1104)).2.2 = 7612444124 := by decide +kernel
  have hp : parent2 (847 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 847 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 847 c] :
    ∀ c ∈ Finset.univ, (alphaQ 847 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 847 i (c.val i) t) =
      ((jwv 847 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 847 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 847 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 847 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 847 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_848 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 848),
        qvalQ (fun t ↦ ∑ i, PE 848 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 848),
        (alphaQ 848 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 848 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 848 = 0 := by decide +kernel
  have hce : certE (848 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (848 : Fin 1104)).2.2 = 20992841631 := by decide +kernel
  have hp : parent2 (848 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 848 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 848 c] :
    ∀ c ∈ Finset.univ, (alphaQ 848 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 848 i (c.val i) t) =
      ((jwv 848 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 848 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 848 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 848 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 848 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_849 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 849),
        qvalQ (fun t ↦ ∑ i, PE 849 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 849),
        (alphaQ 849 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 849 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 849 = 2 := by decide +kernel
  have hce : certE (849 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -13 else if j.val = 1 then 4 else if j.val = 2 then -2 else 2)) := by decide +kernel
  have hs : (l2At (849 : Fin 1104)).2.2 = 19381739695 := by decide +kernel
  have hp : parent2 (849 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 849 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 849 c] :
    ∀ c ∈ Finset.univ, (alphaQ 849 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 849 i (c.val i) t) =
      ((jwv 849 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 849 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 849 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 849 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 849 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_850 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 850),
        qvalQ (fun t ↦ ∑ i, PE 850 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 850),
        (alphaQ 850 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 850 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 850 = 1 := by decide +kernel
  have hce : certE (850 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (850 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (850 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 850 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 850 c] :
    ∀ c ∈ Finset.univ, (alphaQ 850 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 850 i (c.val i) t) =
      ((jwv 850 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 850 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 850 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 850 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 850 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_851 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 851),
        qvalQ (fun t ↦ ∑ i, PE 851 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 851),
        (alphaQ 851 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 851 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 851 = 0 := by decide +kernel
  have hce : certE (851 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (851 : Fin 1104)).2.2 = 20992842075 := by decide +kernel
  have hp : parent2 (851 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 851 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 851 c] :
    ∀ c ∈ Finset.univ, (alphaQ 851 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 851 i (c.val i) t) =
      ((jwv 851 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 851 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 851 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 851 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 851 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_852 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 852),
        qvalQ (fun t ↦ ∑ i, PE 852 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 852),
        (alphaQ 852 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 852 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 852 = 2 := by decide +kernel
  have hce : certE (852 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -22 else if j.val = 1 then 4 else if j.val = 2 then -3 else 6)) := by decide +kernel
  have hs : (l2At (852 : Fin 1104)).2.2 = 18175506034 := by decide +kernel
  have hp : parent2 (852 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 852 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 852 c] :
    ∀ c ∈ Finset.univ, (alphaQ 852 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 852 i (c.val i) t) =
      ((jwv 852 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 852 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 852 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 852 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 852 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_853 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 853),
        qvalQ (fun t ↦ ∑ i, PE 853 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 853),
        (alphaQ 853 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 853 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 853 = 1 := by decide +kernel
  have hce : certE (853 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (853 : Fin 1104)).2.2 = 20924019157 := by decide +kernel
  have hp : parent2 (853 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 853 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 853 c] :
    ∀ c ∈ Finset.univ, (alphaQ 853 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 853 i (c.val i) t) =
      ((jwv 853 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 853 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 853 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 853 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 853 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_854 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 854),
        qvalQ (fun t ↦ ∑ i, PE 854 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 854),
        (alphaQ 854 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 854 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 854 = 0 := by decide +kernel
  have hce : certE (854 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-10 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else 4) else (if j.val = 0 then -28 else if j.val = 1 then 2 else if j.val = 2 then -2 else 8)) := by decide +kernel
  have hs : (l2At (854 : Fin 1104)).2.2 = 7731517250 := by decide +kernel
  have hp : parent2 (854 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 854 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 854 c] :
    ∀ c ∈ Finset.univ, (alphaQ 854 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 854 i (c.val i) t) =
      ((jwv 854 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 854 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 854 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 854 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 854 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_855 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 855),
        qvalQ (fun t ↦ ∑ i, PE 855 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 855),
        (alphaQ 855 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 855 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 855 = 2 := by decide +kernel
  have hce : certE (855 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -9 else if j.val = 1 then -2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hs : (l2At (855 : Fin 1104)).2.2 = 19375903850 := by decide +kernel
  have hp : parent2 (855 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 855 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 855 c] :
    ∀ c ∈ Finset.univ, (alphaQ 855 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 855 i (c.val i) t) =
      ((jwv 855 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 855 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 855 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 855 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 855 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_856 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 856),
        qvalQ (fun t ↦ ∑ i, PE 856 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 856),
        (alphaQ 856 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 856 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 856 = 1 := by decide +kernel
  have hce : certE (856 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (856 : Fin 1104)).2.2 = 20924017544 := by decide +kernel
  have hp : parent2 (856 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 856 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 856 c] :
    ∀ c ∈ Finset.univ, (alphaQ 856 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 856 i (c.val i) t) =
      ((jwv 856 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 856 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 856 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 856 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 856 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_857 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 857),
        qvalQ (fun t ↦ ∑ i, PE 857 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 857),
        (alphaQ 857 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 857 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 857 = 0 := by decide +kernel
  have hce : certE (857 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (857 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (857 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 857 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 857 c] :
    ∀ c ∈ Finset.univ, (alphaQ 857 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 857 i (c.val i) t) =
      ((jwv 857 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 857 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 857 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 857 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 857 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_858 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 858),
        qvalQ (fun t ↦ ∑ i, PE 858 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 858),
        (alphaQ 858 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 858 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 858 = 1 := by decide +kernel
  have hce : certE (858 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -26 else if j.val = 1 then 5 else if j.val = 2 then 2 else 1)) := by decide +kernel
  have hs : (l2At (858 : Fin 1104)).2.2 = 633690026 := by decide +kernel
  have hp : parent2 (858 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 858 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 858 c] :
    ∀ c ∈ Finset.univ, (alphaQ 858 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 858 i (c.val i) t) =
      ((jwv 858 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 858 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 858 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 858 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 858 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_859 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 859),
        qvalQ (fun t ↦ ∑ i, PE 859 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 859),
        (alphaQ 859 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 859 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 859 = 0 := by decide +kernel
  have hce : certE (859 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (859 : Fin 1104)).2.2 = 20992843776 := by decide +kernel
  have hp : parent2 (859 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 859 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 859 c] :
    ∀ c ∈ Finset.univ, (alphaQ 859 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 859 i (c.val i) t) =
      ((jwv 859 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 859 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 859 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 859 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 859 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_860 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 860),
        qvalQ (fun t ↦ ∑ i, PE 860 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 860),
        (alphaQ 860 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 860 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 860 = 1 := by decide +kernel
  have hce : certE (860 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then 12 else if j.val = 1 then 5 else if j.val = 2 then -4 else -8)) := by decide +kernel
  have hs : (l2At (860 : Fin 1104)).2.2 = 276229029 := by decide +kernel
  have hp : parent2 (860 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 860 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 860 c] :
    ∀ c ∈ Finset.univ, (alphaQ 860 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 860 i (c.val i) t) =
      ((jwv 860 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 860 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 860 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 860 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 860 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_861 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 861),
        qvalQ (fun t ↦ ∑ i, PE 861 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 861),
        (alphaQ 861 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 861 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 861 = 0 := by decide +kernel
  have hce : certE (861 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (861 : Fin 1104)).2.2 = 20992830648 := by decide +kernel
  have hp : parent2 (861 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 861 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 861 c] :
    ∀ c ∈ Finset.univ, (alphaQ 861 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 861 i (c.val i) t) =
      ((jwv 861 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 861 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 861 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 861 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 861 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_862 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 862),
        qvalQ (fun t ↦ ∑ i, PE 862 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 862),
        (alphaQ 862 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 862 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 862 = 1 := by decide +kernel
  have hce : certE (862 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then 11 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hs : (l2At (862 : Fin 1104)).2.2 = 276295471 := by decide +kernel
  have hp : parent2 (862 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 862 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 862 c] :
    ∀ c ∈ Finset.univ, (alphaQ 862 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 862 i (c.val i) t) =
      ((jwv 862 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 862 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 862 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 862 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 862 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_863 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 863),
        qvalQ (fun t ↦ ∑ i, PE 863 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 863),
        (alphaQ 863 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 863 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 863 = 0 := by decide +kernel
  have hce : certE (863 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (863 : Fin 1104)).2.2 = 20992843256 := by decide +kernel
  have hp : parent2 (863 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 863 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 863 c] :
    ∀ c ∈ Finset.univ, (alphaQ 863 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 863 i (c.val i) t) =
      ((jwv 863 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 863 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 863 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 863 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 863 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_864 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 864),
        qvalQ (fun t ↦ ∑ i, PE 864 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 864),
        (alphaQ 864 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 864 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 864 = 2 := by decide +kernel
  have hce : certE (864 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (864 : Fin 1104)).2.2 = 21076752184 := by decide +kernel
  have hp : parent2 (864 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 864 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 864 c] :
    ∀ c ∈ Finset.univ, (alphaQ 864 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 864 i (c.val i) t) =
      ((jwv 864 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 864 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 864 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 864 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 864 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_865 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 865),
        qvalQ (fun t ↦ ∑ i, PE 865 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 865),
        (alphaQ 865 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 865 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 865 = 0 := by decide +kernel
  have hce : certE (865 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -2 else if j.val = 1 then -1 else if j.val = 2 then 3 else -5)) := by decide +kernel
  have hs : (l2At (865 : Fin 1104)).2.2 = 619815616 := by decide +kernel
  have hp : parent2 (865 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 865 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 865 c] :
    ∀ c ∈ Finset.univ, (alphaQ 865 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 865 i (c.val i) t) =
      ((jwv 865 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 865 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 865 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 865 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 865 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_866 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 866),
        qvalQ (fun t ↦ ∑ i, PE 866 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 866),
        (alphaQ 866 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 866 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 866 = 2 := by decide +kernel
  have hce : certE (866 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (866 : Fin 1104)).2.2 = 21076756812 := by decide +kernel
  have hp : parent2 (866 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 866 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 866 c] :
    ∀ c ∈ Finset.univ, (alphaQ 866 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 866 i (c.val i) t) =
      ((jwv 866 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 866 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 866 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 866 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 866 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_867 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 867),
        qvalQ (fun t ↦ ∑ i, PE 867 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 867),
        (alphaQ 867 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 867 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 867 = 0 := by decide +kernel
  have hce : certE (867 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -13 else if j.val = 1 then 5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hs : (l2At (867 : Fin 1104)).2.2 = 1186491461 := by decide +kernel
  have hp : parent2 (867 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 867 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 867 c] :
    ∀ c ∈ Finset.univ, (alphaQ 867 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 867 i (c.val i) t) =
      ((jwv 867 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 867 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 867 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 867 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 867 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_868 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 868),
        qvalQ (fun t ↦ ∑ i, PE 868 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 868),
        (alphaQ 868 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 868 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 868 = 2 := by decide +kernel
  have hce : certE (868 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (868 : Fin 1104)).2.2 = 21076742685 := by decide +kernel
  have hp : parent2 (868 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 868 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 868 c] :
    ∀ c ∈ Finset.univ, (alphaQ 868 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 868 i (c.val i) t) =
      ((jwv 868 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 868 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 868 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 868 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 868 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_869 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 869),
        qvalQ (fun t ↦ ∑ i, PE 869 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 869),
        (alphaQ 869 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 869 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 869 = 0 := by decide +kernel
  have hce : certE (869 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -6 else if j.val = 1 then 5 else if j.val = 2 then -3 else -2)) := by decide +kernel
  have hs : (l2At (869 : Fin 1104)).2.2 = 619855251 := by decide +kernel
  have hp : parent2 (869 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 869 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 869 c] :
    ∀ c ∈ Finset.univ, (alphaQ 869 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 869 i (c.val i) t) =
      ((jwv 869 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 869 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 869 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 869 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 869 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_870 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 870),
        qvalQ (fun t ↦ ∑ i, PE 870 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 870),
        (alphaQ 870 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 870 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 870 = 2 := by decide +kernel
  have hce : certE (870 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (870 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (870 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 870 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 870 c] :
    ∀ c ∈ Finset.univ, (alphaQ 870 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 870 i (c.val i) t) =
      ((jwv 870 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 870 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 870 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 870 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 870 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_871 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 871),
        qvalQ (fun t ↦ ∑ i, PE 871 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 871),
        (alphaQ 871 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 871 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 871 = 1 := by decide +kernel
  have hce : certE (871 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -38 else if j.val = 1 then 3 else if j.val = 2 then 2 else 2)) := by decide +kernel
  have hs : (l2At (871 : Fin 1104)).2.2 = 120327 := by decide +kernel
  have hp : parent2 (871 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 871 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 871 c] :
    ∀ c ∈ Finset.univ, (alphaQ 871 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 871 i (c.val i) t) =
      ((jwv 871 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 871 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 871 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 871 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 871 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_872 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 872),
        qvalQ (fun t ↦ ∑ i, PE 872 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 872),
        (alphaQ 872 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 872 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 872 = 0 := by decide +kernel
  have hce : certE (872 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -28 else if j.val = 1 then -5 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hs : (l2At (872 : Fin 1104)).2.2 = 20131360620 := by decide +kernel
  have hp : parent2 (872 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 872 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 872 c] :
    ∀ c ∈ Finset.univ, (alphaQ 872 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 872 i (c.val i) t) =
      ((jwv 872 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 872 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 872 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 872 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 872 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_873 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 873),
        qvalQ (fun t ↦ ∑ i, PE 873 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 873),
        (alphaQ 873 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 873 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 873 = 2 := by decide +kernel
  have hce : certE (873 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -1 else if j.val = 1 then -4 else if j.val = 2 then -8 else 1)) := by decide +kernel
  have hs : (l2At (873 : Fin 1104)).2.2 = 110617 := by decide +kernel
  have hp : parent2 (873 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 873 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 873 c] :
    ∀ c ∈ Finset.univ, (alphaQ 873 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 873 i (c.val i) t) =
      ((jwv 873 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 873 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 873 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 873 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 873 i (a i) t)),
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
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨828 + j.val, by omega⟩),
        qvalQ (fun t ↦ ∑ i, PE ⟨828 + j.val, by omega⟩ i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨828 + j.val, by omega⟩),
        (alphaQ ⟨828 + j.val, by omega⟩ c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE ⟨828 + j.val, by omega⟩ i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.pcert_828
  | ⟨1, _⟩ => exact MME.L2Cert.pcert_829
  | ⟨2, _⟩ => exact MME.L2Cert.pcert_830
  | ⟨3, _⟩ => exact MME.L2Cert.pcert_831
  | ⟨4, _⟩ => exact MME.L2Cert.pcert_832
  | ⟨5, _⟩ => exact MME.L2Cert.pcert_833
  | ⟨6, _⟩ => exact MME.L2Cert.pcert_834
  | ⟨7, _⟩ => exact MME.L2Cert.pcert_835
  | ⟨8, _⟩ => exact MME.L2Cert.pcert_836
  | ⟨9, _⟩ => exact MME.L2Cert.pcert_837
  | ⟨10, _⟩ => exact MME.L2Cert.pcert_838
  | ⟨11, _⟩ => exact MME.L2Cert.pcert_839
  | ⟨12, _⟩ => exact MME.L2Cert.pcert_840
  | ⟨13, _⟩ => exact MME.L2Cert.pcert_841
  | ⟨14, _⟩ => exact MME.L2Cert.pcert_842
  | ⟨15, _⟩ => exact MME.L2Cert.pcert_843
  | ⟨16, _⟩ => exact MME.L2Cert.pcert_844
  | ⟨17, _⟩ => exact MME.L2Cert.pcert_845
  | ⟨18, _⟩ => exact MME.L2Cert.pcert_846
  | ⟨19, _⟩ => exact MME.L2Cert.pcert_847
  | ⟨20, _⟩ => exact MME.L2Cert.pcert_848
  | ⟨21, _⟩ => exact MME.L2Cert.pcert_849
  | ⟨22, _⟩ => exact MME.L2Cert.pcert_850
  | ⟨23, _⟩ => exact MME.L2Cert.pcert_851
  | ⟨24, _⟩ => exact MME.L2Cert.pcert_852
  | ⟨25, _⟩ => exact MME.L2Cert.pcert_853
  | ⟨26, _⟩ => exact MME.L2Cert.pcert_854
  | ⟨27, _⟩ => exact MME.L2Cert.pcert_855
  | ⟨28, _⟩ => exact MME.L2Cert.pcert_856
  | ⟨29, _⟩ => exact MME.L2Cert.pcert_857
  | ⟨30, _⟩ => exact MME.L2Cert.pcert_858
  | ⟨31, _⟩ => exact MME.L2Cert.pcert_859
  | ⟨32, _⟩ => exact MME.L2Cert.pcert_860
  | ⟨33, _⟩ => exact MME.L2Cert.pcert_861
  | ⟨34, _⟩ => exact MME.L2Cert.pcert_862
  | ⟨35, _⟩ => exact MME.L2Cert.pcert_863
  | ⟨36, _⟩ => exact MME.L2Cert.pcert_864
  | ⟨37, _⟩ => exact MME.L2Cert.pcert_865
  | ⟨38, _⟩ => exact MME.L2Cert.pcert_866
  | ⟨39, _⟩ => exact MME.L2Cert.pcert_867
  | ⟨40, _⟩ => exact MME.L2Cert.pcert_868
  | ⟨41, _⟩ => exact MME.L2Cert.pcert_869
  | ⟨42, _⟩ => exact MME.L2Cert.pcert_870
  | ⟨43, _⟩ => exact MME.L2Cert.pcert_871
  | ⟨44, _⟩ => exact MME.L2Cert.pcert_872
  | ⟨45, _⟩ => exact MME.L2Cert.pcert_873
  | ⟨n + 46, h⟩ => exact absurd h (by omega)
