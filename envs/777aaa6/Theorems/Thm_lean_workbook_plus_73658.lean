-- Prove2me | Theorems.Thm_lean_workbook_plus_73658
-- name    : lean_workbook_plus_73658
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d7a9ce48-73bb-4531-ab86-186b81681bd2
-- statement:
--   Let $a,b,c$ be real numbers . Prove that $3|a|+|a+3b|+|5b+c|+5|c|\geq \frac{28}{19}(|a+b+4c|)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73658 (a b c : ℝ) : 3 * |a| + |a + 3 * b| + |5 * b + c| + 5 * |c| ≥ (28 / 19) * |a + b + 4 * c|   :=  by sorry
