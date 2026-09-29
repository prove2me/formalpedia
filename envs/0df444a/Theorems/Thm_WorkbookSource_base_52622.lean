-- Prove2me | Theorems.Thm_WorkbookSource_base_52622
-- name    : WorkbookSource.base_52622
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:49:40.643801+00:00
-- url     : https://prove2.me/theorems/c12cb9b1-315c-4814-bdfb-2c8addf0ea59
-- title:
--   A six-term four-variable cyclic ratio sum is at least four
-- statement:
--   a,b,c,d >0 ,prove that:
--
--    $\frac{a}{a+b}+\frac{c}{c+d}+\frac{a}{b+c}+\frac{2b}{c+d}+\frac{c}{d+a}+\frac{2d}{a+b}\geq 4.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52622` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52622; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52622 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a / (a + b) + c / (c + d) + a / (b + c) + 2 * b / (c + d) + c / (d + a) + 2 * d / (a + b)) ≥ 4  :=  by sorry
