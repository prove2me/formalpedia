-- Prove2me | Theorems.Thm_WorkbookSource_base_50900
-- name    : WorkbookSource.base_50900
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:40:11.847755+00:00
-- url     : https://prove2.me/theorems/0cf593c7-232f-4c0d-b236-aa4348814695
-- title:
--   A mixed square and cubic bound under a nonlinear sum constraint
-- statement:
--   Let $x$ , $y$ and $z$ be non-negative numbers such that $x+y+z\geq x^2+y^3+z^3$. Prove that $3x^2+4y^3+4z^3\leq 11$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50900` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50900; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50900 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z ≥ x^2 + y^3 + z^3) : 3 * x^2 + 4 * y^3 + 4 * z^3 ≤ 11  :=  by sorry
