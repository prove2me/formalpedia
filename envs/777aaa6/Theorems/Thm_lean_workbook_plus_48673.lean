-- Prove2me | Theorems.Thm_lean_workbook_plus_48673
-- name    : lean_workbook_plus_48673
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/6f3e65af-dde7-4cd3-bedd-11862194ba7b
-- statement:
--   Prove that $\frac{a^2}{(b+1)(c+1)}+\frac{b^2}{(c+1)(a+1)}+\frac{c^2}{(a+1)(b+1)}+\frac{2abc}{(a+1)(b+1)(c+1)}\ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48673 : ∀ a b c : ℝ, (a^2 / (b + 1) / (c + 1) + b^2 / (c + 1) / (a + 1) + c^2 / (a + 1) / (b + 1) + 2 * a * b * c / (a + 1) / (b + 1) / (c + 1)) ≥ 1   :=  by sorry
