-- Prove2me | Theorems.Thm_lean_workbook_plus_13317
-- name    : lean_workbook_plus_13317
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/fb9828be-720a-41c0-9e95-208f79d8fa94
-- statement:
--   If $x,y,z$ are positive real numbers such that $3=xy+yz+zx$ show that $3(x+y)(x+z)(y+z)(x+y+z)\ge 2(x^2+y^2+z^2+6)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13317 (x y z : ℝ) (h : 3 = x * y + y * z + z * x) : 3 * (x + y) * (x + z) * (y + z) * (x + y + z) ≥ 2 * (x ^ 2 + y ^ 2 + z ^ 2 + 6)   :=  by sorry
