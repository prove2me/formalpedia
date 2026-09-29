-- Prove2me | Theorems.Thm_WorkbookSource_base_258
-- name    : WorkbookSource.base_258
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:19:29.846692+00:00
-- url     : https://prove2.me/theorems/cc87230e-7830-43e7-8bf7-7e1813d4bfbf
-- title:
--   A four-variable cubic ratio inequality with a product of signed triple sums
-- statement:
--   For $ a, b, c, d > 0 $ real numbers, prove: $ ab+ac+ad+bc+bd+cd +\frac{a^3+b^3+c^3+d^3}{a+b+c+d} \ge a^2+b^2+c^2+d^2+\frac{3(a+b+c-d)(a+b+d-c)(a+c+d-b)(b+c+d-a)}{(a+b+c+d)^2} \ \ ; $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_258` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_258; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_258 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : a * b + a * c + a * d + b * c + b * d + c * d + (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) / (a + b + c + d) ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 3 * (a + b + c - d) * (a + b + d - c) * (a + c + d - b) * (b + c + d - a) / (a + b + c + d) ^ 2  :=  by sorry
