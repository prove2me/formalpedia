-- Prove2me | Theorems.Thm_lean_workbook_plus_5361
-- name    : lean_workbook_plus_5361
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0e620928-bda4-44d9-bf5f-cc0d81bff758
-- statement:
--   (4(x^{2}+y^{2}+z^{2}))^{3}\geq 27\prod (2x^{2}+y^{2}+z^{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5361 (x y z : ℝ) : (4 * (x ^ 2 + y ^ 2 + z ^ 2)) ^ 3 ≥ 27 * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2)   :=  by sorry
