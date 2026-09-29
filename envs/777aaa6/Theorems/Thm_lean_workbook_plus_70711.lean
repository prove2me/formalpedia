-- Prove2me | Theorems.Thm_lean_workbook_plus_70711
-- name    : lean_workbook_plus_70711
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/709b1e40-3b83-4b60-8b78-267691affa40
-- statement:
--   Prove the identity: $ \frac1{(4n - 3)(4n - 1)} = \frac12(\frac1{4n - 3} - \frac1{4n - 1})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70711 (n : ℕ) (hn : n ≠ 0) : (1 : ℝ) / ((4 * n - 3) * (4 * n - 1)) = 1 / 2 * (1 / (4 * n - 3) - 1 / (4 * n - 1))   :=  by sorry
