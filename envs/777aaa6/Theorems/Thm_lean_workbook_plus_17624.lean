-- Prove2me | Theorems.Thm_lean_workbook_plus_17624
-- name    : lean_workbook_plus_17624
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/9f63c3fb-67ce-4ff2-b554-87443dd969f8
-- statement:
--   Let $x,y>0$ ,prove that: $2.\frac{1}{x}\geq \frac{4}{(1+x)^2} \Leftrightarrow (1+x)^2\geq 4x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17624 (x : ℝ) (hx : 0 < x) :
  2 * (1 / x) ≥ 4 / (1 + x) ^ 2 ↔ (1 + x) ^ 2 ≥ 4 * x   :=  by sorry
