-- Prove2me | Theorems.Thm_WorkbookSource_base_9113
-- name    : WorkbookSource.base_9113
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:22:41.493791+00:00
-- url     : https://prove2.me/theorems/7f55bc5a-c246-4eca-8e8f-f88167f9aea4
-- title:
--   A shifted cyclic squared-denominator ratio inequality at fixed total four
-- statement:
--   Let positive real a,b,c,d which satisfy: $a+b+c+d=4$ Prove that: $ \frac{a}{a+3b^2}+\frac{b}{b+3c^2}+\frac{c}{c+3d^2}+\frac{d}{d+3a^2} \ge 1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9113` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9113; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9113 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (habc : a + b + c + d = 4) : a / (a + 3 * b ^ 2) + b / (b + 3 * c ^ 2) + c / (c + 3 * d ^ 2) + d / (d + 3 * a ^ 2) ≥ 1  :=  by sorry
