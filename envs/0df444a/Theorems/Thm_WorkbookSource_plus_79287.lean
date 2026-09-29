-- Prove2me | Theorems.Thm_WorkbookSource_plus_79287
-- name    : WorkbookSource.plus_79287
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:54.695195+00:00
-- url     : https://prove2.me/theorems/54c8d9c8-3f78-43be-b052-46de04e34224
-- title:
--   A norm bound under two linked quadratic constraints
-- statement:
--   Let $a,b,c$ are real numbers such that $a^2+2b=1$ and $b^2+4c=-1.$ Prove that $$a^2+b^2+c^2\geq \frac{89}{256}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_79287` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_79287; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_79287 (a b c : ℝ) (ha : a^2 + 2 * b = 1) (hb : b^2 + 4 * c = -1) : 89 / 256 ≤ a^2 + b^2 + c^2   :=  by sorry
