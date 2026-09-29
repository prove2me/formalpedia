-- Prove2me | Theorems.Thm_mme_released_recursive_level3_compat22
-- name    : mme_released_recursive_level3_compat22
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T09:45:44.804986+00:00
-- url     : https://prove2.me/theorems/1f1fb4d0-3a7a-400a-aa02-8cbfb6ec10e2
-- title:
--   Compatibility potential ceilings for regions 67 to 74 of level-three band 1
-- statement:
--   A rational upper bound on the compatibility potential for 80 compatibility parts of
--   level-three band 1, covering regions 67 to 74.
--
--   The splits of a region are grouped -- boundary cells individually, the rest by their grade in the
--   relevant mode -- and each group contributes one term to the potential. The bound is the ceiling a
--   table of small-prime references assigns to each group's normalised word distribution.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem mme_released_recursive_level3_compat22 :
    (regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(67 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(67 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(67 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (97713164952358533434734140925 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(68 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(68 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (403688030147559058388543137439 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(68 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(68 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (253811735066344604179045877099 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(68 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (180787233011069082900563750203 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (425452593031168689765847342612 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (207952748835078924617044506476 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(69 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (399087406721834544591898324694 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(69 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(69 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (416576863472930549010038474028 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(69 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (433339730061456770171035698320 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(69 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(70 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(70 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(70 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(70 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (5079302912876786893097867341 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(70 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (370690263124338376936692351439 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (5325515105065912187509482 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(71 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (333809287567561481136762530714 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(71 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(71 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(71 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (149314712819873506805714555 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(71 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (335830734595571012315509688661 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(71 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(71 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(72 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(72 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(72 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (304607222871188007383515463126 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(72 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(72 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(73 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(73 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(73 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(73 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((74 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(74 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (203944561724222188896401499133 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(74 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) := by sorry
