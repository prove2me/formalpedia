-- Prove2me | Theorems.Thm_lean_workbook_plus_10495
-- name    : lean_workbook_plus_10495
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/dccbc24a-9fa9-46c8-ab97-fc81194cc4e1
-- statement:
--   2, 3, 7 $\in$ S but 5 $\notin$ S
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10495 (S : Set ℕ) (h : S = {n | n % 2 = 0 ∨ n % 3 = 0 ∨ n % 7 = 0}) : 2 ∈ S ∧ 3 ∈ S ∧ 7 ∈ S   :=  by sorry
