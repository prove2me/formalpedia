-- Prove2me | Theorems.Thm_lean_workbook_plus_9810
-- name    : lean_workbook_plus_9810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/1f7cb9e5-4074-4a2c-92cc-d6d58baf4618
-- statement:
--   Consider $S:=x^4+y^4+z^4-2y^2z^2-2z^2x^2-2x^2y^2=-(x+y+z)(y+z-x)(z+x-y)(x+y-z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9810 : ∀ x y z : ℝ, x ^ 4 + y ^ 4 + z ^ 4 - 2 * y ^ 2 * z ^ 2 - 2 * z ^ 2 * x ^ 2 - 2 * x ^ 2 * y ^ 2 = -(x + y + z) * (y + z - x) * (z + x - y) * (x + y - z)   :=  by sorry
