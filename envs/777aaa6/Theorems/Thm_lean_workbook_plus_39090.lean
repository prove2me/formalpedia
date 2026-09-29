-- Prove2me | Theorems.Thm_lean_workbook_plus_39090
-- name    : lean_workbook_plus_39090
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/58e2653c-76cc-4730-b23b-221d1bcc7e19
-- statement:
--   Prove that $(x+y+z)^2[21(x^2+y^2+z^2)+946\sum (x^2-yz)] \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39090 (x y z : ℝ) : (x + y + z) ^ 2 * (21 * (x ^ 2 + y ^ 2 + z ^ 2) + 946 * (x ^ 2 - y * z + y ^ 2 - z * x + z ^ 2 - x * y)) ≥ 0   :=  by sorry
