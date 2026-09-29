-- Prove2me | Theorems.Thm_lean_workbook_plus_65615
-- name    : lean_workbook_plus_65615
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/8bd59a6e-c99a-4a19-af1d-d9d17cc9f934
-- statement:
--   Setting $t = x - \frac{12}{x}$ , \n\n $t^{2} + 24 = 10t$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65615 (x : ℝ) (hx: x ≠ 0) (t : ℝ) (ht : t = x - 12/x) : t^2 + 24 = 10*t ↔ t = 4 ∨ t = 6   :=  by sorry
