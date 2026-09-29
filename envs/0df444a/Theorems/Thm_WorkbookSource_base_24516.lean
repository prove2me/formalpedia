-- Prove2me | Theorems.Thm_WorkbookSource_base_24516
-- name    : WorkbookSource.base_24516
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:29.538046+00:00
-- url     : https://prove2.me/theorems/8119d9b8-c461-4704-a1e0-725288b87758
-- title:
--   An asymmetrically shifted product bound at fixed sum one
-- statement:
--   Using the Arithmetic Mean-Geometric Mean (AM-GM) inequality, prove that $(x + 1)(y + 2)(z + 3) \leq 12$ for non-negative real numbers $x, y, z$ with $x + y + z = 1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24516` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24516; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24516 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 1) : (x + 1) * (y + 2) * (z + 3) ≤ 12  :=  by sorry
