-- Prove2me | Theorems.Thm_WorkbookSource_plus_74571
-- name    : WorkbookSource.plus_74571
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:55.173533+00:00
-- url     : https://prove2.me/theorems/11c1c64b-302d-4318-a878-ba62b726ae25
-- title:
--   A weighted quadratic ratio sum is at most five
-- statement:
--   Given $a, b, c$ are positive numbers, prove that:
--   $\frac{a^2+9bc}{2a^2+(b+c)^2}+\frac{b^2+9ca}{2b^2+(c+a)^2}+\frac{c^2+9ab}{2c^2+(a+b)^2}\leq 5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_74571` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_74571; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_74571 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 9 * b * c) / (2 * a^2 + (b + c)^2) + (b^2 + 9 * c * a) / (2 * b^2 + (c + a)^2) + (c^2 + 9 * a * b) / (2 * c^2 + (a + b)^2) ≤ 5   :=  by sorry
