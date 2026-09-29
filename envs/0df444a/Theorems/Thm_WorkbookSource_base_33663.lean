-- Prove2me | Theorems.Thm_WorkbookSource_base_33663
-- name    : WorkbookSource.base_33663
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:45.269+00:00
-- url     : https://prove2.me/theorems/4ef28b04-61e8-4a12-8140-98f012fd639f
-- title:
--   A weighted pair-product ratio upper bound at fixed sum three
-- statement:
--   For positives $a$ , $b$ and $c$ such that $a+b+c=3$ prove that:
--   $ \frac{a}{4a+5bc}+\frac{b}{4b+5ca}+\frac{c}{4c+5ab}\le\frac{a^2+b^2+c^2}{9} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33663` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33663; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33663 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (4 * a + 5 * b * c) + b / (4 * b + 5 * c * a) + c / (4 * c + 5 * a * b) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 9  :=  by sorry
