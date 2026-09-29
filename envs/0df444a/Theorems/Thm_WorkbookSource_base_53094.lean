-- Prove2me | Theorems.Thm_WorkbookSource_base_53094
-- name    : WorkbookSource.base_53094
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:03:46.126088+00:00
-- url     : https://prove2.me/theorems/c2e0cec6-dcca-4ed6-8547-3437079b925c
-- title:
--   A shifted cyclic quadratic ratio bounds the quadratic sum
-- statement:
--   For $a, b, c>0, a+b+c=3$ prove that
--    $\frac{a(a+2)}{a(b+3)+2}+\frac{b(b+2)}{b(c+3)+2}+\frac{c(c+2)}{c(a+3)+2}\le\frac{a^2+b^2+c^2}{2}$
--   Happy New Year to all Mathlinkers !
--   With the greatest respect,
--   oldbeginner
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53094` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53094; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53094 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a * (a + 2) / (a * (b + 3) + 2) + b * (b + 2) / (b * (c + 3) + 2) + c * (c + 2) / (c * (a + 3) + 2) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2  :=  by sorry
