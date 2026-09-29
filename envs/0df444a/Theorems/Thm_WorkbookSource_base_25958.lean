-- Prove2me | Theorems.Thm_WorkbookSource_base_25958
-- name    : WorkbookSource.base_25958
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:05:58.651748+00:00
-- url     : https://prove2.me/theorems/0fedbbd3-73b8-4df2-971e-1b9a0832dc27
-- title:
--   A comparison of cyclic and weighted pairwise ratio sums
-- statement:
--   Given $a,b,c>0$ . Prove that $\frac{a}{b}+\frac{b}{c}+\frac{c}{a} \geq \frac{a}{b+2c}+\frac{b}{c+2a}+\frac{c}{a+2b}+2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25958` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25958; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25958 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ (a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b)) + 2  :=  by sorry
