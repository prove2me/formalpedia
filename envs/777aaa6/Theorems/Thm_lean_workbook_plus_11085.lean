-- Prove2me | Theorems.Thm_lean_workbook_plus_11085
-- name    : lean_workbook_plus_11085
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/d90de434-10c8-4032-9c94-9d4796203489
-- statement:
--   $ \frac{\frac{2}{3}\cdot 10}{8}=\frac{\frac{1}{2}\cdot 5}{x}$ ...then $ x=3$ . $ \boxed{C}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11085  (x : ℝ)
  (h₀ : 2 / 3 * 10 / 8 = 1 / 2 * 5 / x) :
  x = 3   :=  by sorry
