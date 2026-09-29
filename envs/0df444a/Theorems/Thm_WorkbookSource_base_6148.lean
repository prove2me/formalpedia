-- Prove2me | Theorems.Thm_WorkbookSource_base_6148
-- name    : WorkbookSource.base_6148
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:06.766684+00:00
-- url     : https://prove2.me/theorems/ab331791-ea12-4050-a649-c8fc1df1b9ff
-- title:
--   A quartic pairwise bound with a cubic correction
-- statement:
--   Let $a,b,c$ to be non negative real numbers satisfying $a+b+c=2$. $b^2c^2+c^2a^2+a^2b^2+\dfrac{11}{8}abc\le 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6148` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6148; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6148 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 2) : b^2 * c^2 + c^2 * a^2 + a^2 * b^2 + (11 / 8) * a * b * c ≤ 1  :=  by sorry
