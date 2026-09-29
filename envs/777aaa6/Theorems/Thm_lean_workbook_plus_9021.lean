-- Prove2me | Theorems.Thm_lean_workbook_plus_9021
-- name    : lean_workbook_plus_9021
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3e113371-1231-41ae-8a60-cb81e73507e2
-- statement:
--   Cauchy-Schwarz inequality: $(a^2+b^2+c^2)(x^2+y^2+z^2)\geq (ax+by+cz)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9021 (a b c x y z : ℝ) :
  (a^2 + b^2 + c^2) * (x^2 + y^2 + z^2) ≥ (a * x + b * y + c * z)^2   :=  by sorry
