-- Prove2me | Theorems.Thm_lean_workbook_plus_40700
-- name    : lean_workbook_plus_40700
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d04df885-29d5-4b85-8e57-7ad9069b1e8e
-- statement:
--   Prove that $\sum_{cyc} a^2bc \leq \sum_{cyc} a^2b^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40700 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2   :=  by sorry
