-- Prove2me | Theorems.Thm_lean_workbook_plus_47298
-- name    : lean_workbook_plus_47298
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ce4f32d2-3a39-4f7e-aedd-4c5f6fac1654
-- statement:
--   If all the elements of Set $A$ can be found in Set $B$ , but not vice-versa, $A$ is a proper subset of $B$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47298 {A B : Set α} (h₁ : A ⊆ B) (h₂ : ¬ B ⊆ A) : A ⊂ B   :=  by sorry
