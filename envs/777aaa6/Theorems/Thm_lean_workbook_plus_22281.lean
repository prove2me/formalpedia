-- Prove2me | Theorems.Thm_lean_workbook_plus_22281
-- name    : lean_workbook_plus_22281
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/4b8d6494-cbf7-4f2a-88a7-6e4bdf598f44
-- statement:
--   Let $a>3$, $b>3$ and $c>3$. Prove that $ab+bc+ca<abc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22281 (a b c : ℝ) (h1 : 3 < a) (h2 : 3 < b) (h3 : 3 < c) : a * b + b * c + c * a < a * b * c   :=  by sorry
