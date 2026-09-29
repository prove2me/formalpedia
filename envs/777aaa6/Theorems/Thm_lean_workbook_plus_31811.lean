-- Prove2me | Theorems.Thm_lean_workbook_plus_31811
-- name    : lean_workbook_plus_31811
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a736448c-5b88-4b9b-9d72-e9a2dc076844
-- statement:
--   $\iff$ $a\ge |x|$ or $a\ge |x|-\sqrt{2x^2-2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31811 (a x : ℝ) : |x| - Real.sqrt (2 * x ^ 2 - 2) ≤ a ↔ |x| ≤ a ∨ a ≥ |x| - Real.sqrt (2 * x ^ 2 - 2)   :=  by sorry
