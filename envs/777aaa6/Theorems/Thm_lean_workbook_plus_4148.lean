-- Prove2me | Theorems.Thm_lean_workbook_plus_4148
-- name    : lean_workbook_plus_4148
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/247492c4-bebe-4a86-b199-7cbb794fedc9
-- statement:
--   Prove that $x^4+y^4+z^4 \geq x^2yz+y^2zx+z^2xy$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4148 (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 ≥ x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y   :=  by sorry
