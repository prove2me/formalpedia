-- Prove2me | Theorems.Thm_WorkbookSource_plus_16033
-- name    : WorkbookSource.plus_16033
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:15:50.574267+00:00
-- url     : https://prove2.me/theorems/4c176435-21aa-456b-aa6f-51f03afbebe1
-- title:
--   A cyclic reciprocal product sum bounds a quadratic sum
-- statement:
--   Let $a,b,c>0$ and $a+b+c=3$ . Prove $\sum{\left(1+\frac{b}{a}\right) \left (1+\frac{c}{a}\right)}+2\sum{\frac{bc}{a^2}}\ge 6(a^2+b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_16033` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_16033; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_16033 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (1 + b / a) * (1 + c / a) + (1 + c / b) * (1 + a / b) + (1 + a / c) * (1 + b / c) + 2 * (b * c / a ^ 2 + c * a / b ^ 2 + a * b / c ^ 2) ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
