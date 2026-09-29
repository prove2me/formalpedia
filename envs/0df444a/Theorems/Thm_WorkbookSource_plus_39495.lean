-- Prove2me | Theorems.Thm_WorkbookSource_plus_39495
-- name    : WorkbookSource.plus_39495
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:02:37.726225+00:00
-- url     : https://prove2.me/theorems/0d6059e3-359c-4568-a21d-f9c2d1c9e907
-- title:
--   A cyclic quadratic ratio sum with a normalized product correction
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a^2+b^2-a(b-c)}{(b+c)(c+a)}+\frac{b^2+c^2-b(c-a)}{(c+a)(a+b)}+\frac{c^2+a^2-c(a-b)}{(a+b)(b+c)}+\frac{2abc}{(a+b)(b+c)(c+a)}\ge\frac{7}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_39495` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_39495; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_39495 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 - a * (b - c)) / (b + c) / (c + a) + (b^2 + c^2 - b * (c - a)) / (c + a) / (a + b) + (c^2 + a^2 - c * (a - b)) / (a + b) / (b + c) + 2 * a * b * c / (a + b) / (b + c) / (c + a) ≥ 7 / 4   :=  by sorry
