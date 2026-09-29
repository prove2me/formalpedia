-- Prove2me | Theorems.Thm_lean_workbook_plus_76451
-- name    : lean_workbook_plus_76451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/64b196b7-332e-4945-a8f5-0610a27bb84f
-- statement:
--   Let $a,b,c$ be real numbers . Prove that $3|a|+|a+2b|+|5b+c|+7|c|\geq \frac{37}{24}(|a+b+5c|)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76451 (a b c : ℝ) : 3 * |a| + |a + 2 * b| + |5 * b + c| + 7 * |c| ≥ (37 / 24) * |a + b + 5 * c|   :=  by sorry
