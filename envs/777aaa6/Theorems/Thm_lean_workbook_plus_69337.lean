-- Prove2me | Theorems.Thm_lean_workbook_plus_69337
-- name    : lean_workbook_plus_69337
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/017d2ec5-8d5f-447c-92c5-795699301bed
-- statement:
--   Prove that: \n $ \sqrt {x^2 + xy + y^2}\ge \frac {\sqrt {3}}{2}(x + y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69337 (x y : ℝ) : Real.sqrt (x ^ 2 + x * y + y ^ 2) ≥ Real.sqrt 3 / 2 * (x + y)   :=  by sorry
