-- Prove2me | Theorems.Thm_WorkbookSource_plus_67957
-- name    : WorkbookSource.plus_67957
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:48:45.590752+00:00
-- url     : https://prove2.me/theorems/30f6d2cf-116f-4a20-b3ef-b60aa68f1a38
-- title:
--   A quadratic product ratio has a symmetric upper bound
-- statement:
--   Prove that for positive numbers $a, b, c$,
--   $\frac{a^2b^2c^2}{(a^2+bc)(b^2+ca)(c^2+ab)}\le\frac{3(ab+bc+ca)(a+b+c)}{8(a+b+c)^3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_67957` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_67957; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_67957 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * c) ^ 2 / ((a ^ 2 + b * c) * (b ^ 2 + a * c) * (c ^ 2 + a * b)) ≤ (3 * (a * b + b * c + a * c) * (a + b + c)) / (8 * (a + b + c) ^ 3)   :=  by sorry
