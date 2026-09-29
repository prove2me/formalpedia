-- Prove2me | Theorems.Thm_lean_workbook_plus_65958
-- name    : lean_workbook_plus_65958
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/18c42c1f-d93b-4900-a42c-710f07d4af0e
-- statement:
--   Prove that for any natural number $n \geq 6$ , then $$(n+3)^3 \leq 3^n$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65958 (n : ℕ) (h₁ : 6 ≤ n) : (n + 3) ^ 3 ≤ 3 ^ n   :=  by sorry
