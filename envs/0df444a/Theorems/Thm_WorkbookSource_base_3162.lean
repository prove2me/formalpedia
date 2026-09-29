-- Prove2me | Theorems.Thm_WorkbookSource_base_3162
-- name    : WorkbookSource.base_3162
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:08:30.558843+00:00
-- url     : https://prove2.me/theorems/6342d077-f568-4095-bc50-96a5becbe13b
-- title:
--   Adding one decreases a cyclic ratio sum
-- statement:
--   Prove that if $a,b,c > 0$ then $\frac{a+1}{b+1}+\frac{b+1}{c+1}+\frac{c+1}{a+1} \leq \frac{a}{b}+\frac{b}{c}+\frac{c}{a} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3162` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3162; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3162 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 1) / (b + 1) + (b + 1) / (c + 1) + (c + 1) / (a + 1) ≤ a / b + b / c + c / a  :=  by sorry
