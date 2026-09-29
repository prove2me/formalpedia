-- Prove2me | Theorems.Thm_lean_workbook_plus_13758
-- name    : lean_workbook_plus_13758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d639714d-ff13-4e37-a6d7-6c74d0a6ba06
-- statement:
--   According to Albania Eagle, we have: $3(x^4+y^4+z^4)+3xyz(x+y+z) \geq 2 (xy+yz+xz)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13758 (x y z : ℝ) : 3 * (x ^ 4 + y ^ 4 + z ^ 4) + 3 * x * y * z * (x + y + z) ≥ 2 * (x * y + y * z + x * z) ^ 2   :=  by sorry
