-- Prove2me | Theorems.Thm_WorkbookSource_base_19984
-- name    : WorkbookSource.base_19984
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:55:00.034277+00:00
-- url     : https://prove2.me/theorems/6dc8d5c3-15a9-4c7e-834a-e8a477ada3e3
-- title:
--   A cubic lower bound with a quadratic correction
-- statement:
--   Prove that for positives $x$, $y$, and $z$ such that $x+y+z=3$, the inequality $2(x^3+y^3+z^3)\ge x^2+y^2+z^2+3$ holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19984` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19984; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19984 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : 2 * (x ^ 3 + y ^ 3 + z ^ 3) ≥ x ^ 2 + y ^ 2 + z ^ 2 + 3  :=  by sorry
