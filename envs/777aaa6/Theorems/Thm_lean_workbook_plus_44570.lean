-- Prove2me | Theorems.Thm_lean_workbook_plus_44570
-- name    : lean_workbook_plus_44570
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/00448bb1-4181-4fbc-bd66-39c3ab910e54
-- statement:
--   Prove that $4(x+y)(y+z)(z+x) \geq 4zx(2y+z+x)+y(2z+x+y)(2x+y+z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44570 : ∀ x y z : ℝ, 4 * (x + y) * (y + z) * (z + x) ≥ 4 * z * x * (2 * y + z + x) + y * (2 * z + x + y) * (2 * x + y + z)   :=  by sorry
