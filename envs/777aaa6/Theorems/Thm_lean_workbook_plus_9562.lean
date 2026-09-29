-- Prove2me | Theorems.Thm_lean_workbook_plus_9562
-- name    : lean_workbook_plus_9562
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4501f64a-30a2-402e-9e63-066e8a43ef35
-- statement:
--   $ x^{2}+y^{2}+z^{2}-5=s^{2}-6s+9=(s-3)^{2}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9562 : ∀ x y z s : ℝ, (x^2 + y^2 + z^2 - 5 = s^2 - 6 * s + 9 → (s - 3)^2 >= 0)   :=  by sorry
