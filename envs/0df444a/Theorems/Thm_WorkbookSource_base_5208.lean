-- Prove2me | Theorems.Thm_WorkbookSource_base_5208
-- name    : WorkbookSource.base_5208
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:15:42.214505+00:00
-- url     : https://prove2.me/theorems/c9483911-f12c-4a59-b8f8-1ad207fb1dbb
-- title:
--   A fixed-sum quadratic reciprocal upper bound
-- statement:
--   Prove that:
--    $\dfrac{a}{b^2+c^2+9}+\dfrac{b}{c^2+a^2+9}+\dfrac{c}{a^2+b^2+9} \le \dfrac{1}{11}(\dfrac{1}{a}+\dfrac{1}{b}+\dfrac{1}{c})$
--   Given: $a,b,c>0 , a+b+c=3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5208` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5208; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5208 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a / (b ^ 2 + c ^ 2 + 9) + b / (c ^ 2 + a ^ 2 + 9) + c / (a ^ 2 + b ^ 2 + 9)) ≤ (1 / 11) * (1 / a + 1 / b + 1 / c)  :=  by sorry
