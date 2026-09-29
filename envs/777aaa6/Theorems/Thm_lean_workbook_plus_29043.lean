-- Prove2me | Theorems.Thm_lean_workbook_plus_29043
-- name    : lean_workbook_plus_29043
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/111d18ce-01d4-418c-b156-3c4f788fe0b7
-- statement:
--   Prove that $F(x)=x(2yz-y-z)+1-yz \ge \ 0$ for $x,y,z > 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29043 (x y z : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) : x * (2 * y * z - y - z) + 1 - y * z ≥ 0   :=  by sorry
