-- Prove2me | Theorems.Thm_WorkbookSource_base_2198
-- name    : WorkbookSource.base_2198
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:39.830882+00:00
-- url     : https://prove2.me/theorems/d322c9aa-823d-405b-959b-f44b6123a04c
-- title:
--   A mixed cubic and quartic upper bound
-- statement:
--   Let $x, y > 0$ and $x^3 + y^3\leq 2$ . Prove that $x^2 + y^3 \leq x^3 + y^4+\frac{1753}{6912}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2198` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2198; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2198 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 ≤ 2) :  x^2 + y^3 ≤ x^3 + y^4 + 1753 / 6912  :=  by sorry
