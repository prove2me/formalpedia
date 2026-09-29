-- Prove2me | Theorems.Thm_lean_workbook_plus_32028
-- name    : lean_workbook_plus_32028
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/61bc9c96-c698-480c-9aa3-7c254e05a074
-- statement:
--   Let $x$ , $y$ , and $z$ be positive real numbers with $x+y+z = 3$ . Prove that at least one of the three numbers\n\n $x(x+y-z)$\n $y(y+z-x)$\n $z(z+x-y)$\nis less or equal $1$ .\n\n(Karl Czakler)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32028 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : ∃ x y z : ℝ, (x + y + z = 3 ∧ (x * (x + y - z) ≤ 1 ∨ y * (y + z - x) ≤ 1 ∨ z * (z + x - y) ≤ 1))   :=  by sorry
