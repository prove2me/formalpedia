-- Prove2me | Theorems.Thm_lean_workbook_plus_20628
-- name    : lean_workbook_plus_20628
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/edfa6a0f-caa9-436a-bea3-77edb7df185b
-- statement:
--   1) $\sqrt{36x^4-40x^2+4}=2\sqrt{(1-x)(1+x)(1-3x)(1+3x)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20628 (x : ℝ) : Real.sqrt (36 * x ^ 4 - 40 * x ^ 2 + 4) = 2 * Real.sqrt ((1 - x) * (1 + x) * (1 - 3 * x) * (1 + 3 * x))   :=  by sorry
