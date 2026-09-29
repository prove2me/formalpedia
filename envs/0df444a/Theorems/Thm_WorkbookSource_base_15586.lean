-- Prove2me | Theorems.Thm_WorkbookSource_base_15586
-- name    : WorkbookSource.base_15586
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:22:37.809989+00:00
-- url     : https://prove2.me/theorems/d5de12d1-4050-4f12-a34d-9372b3db7846
-- title:
--   A four-variable weighted linear difference ratio sum is nonnegative
-- statement:
--   $a,b,c,d>0$ ,prove
--
--    ${\frac {3\,d-a-b-c}{2\,{a}^{2}+2\,{b}^{2}+2\,{c}^{2}+d \left( a+b+c \right) }}+{\frac {3\,a-b-c-d}{2\,{b}^{2}+2\,{c}^{2}+2\,{d}^{2}+a \left( b+c+d \right) }}+{\frac {3\,b-c-d-a}{2\,{c}^{2}+2\,{d}^{2}+2\,{a}^{2}+b \left( a+c+d \right) }}+{\frac {3\,c-d-a-b}{2\,{d}^{2}+2\,{a}^{2}+2\,{b}^{2}+c \left( d+a+b \right) }}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15586` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15586; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15586 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (3 * d - a - b - c) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + d * (a + b + c)) + (3 * a - b - c - d) / (2 * b ^ 2 + 2 * c ^ 2 + 2 * d ^ 2 + a * (b + c + d)) + (3 * b - c - d - a) / (2 * c ^ 2 + 2 * d ^ 2 + 2 * a ^ 2 + b * (a + c + d)) + (3 * c - d - a - b) / (2 * d ^ 2 + 2 * a ^ 2 + 2 * b ^ 2 + c * (d + a + b)) ≥ 0  :=  by sorry
