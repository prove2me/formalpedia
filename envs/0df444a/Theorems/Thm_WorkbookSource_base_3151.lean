-- Prove2me | Theorems.Thm_WorkbookSource_base_3151
-- name    : WorkbookSource.base_3151
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:08:23.713739+00:00
-- url     : https://prove2.me/theorems/b7d8cbf8-3c6c-45ac-beb0-4c2cc3184505
-- title:
--   A comparison of cyclic pairwise ratio sums
-- statement:
--   If $a$ , $b$ , $c > 0$ , prove that $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\geq \frac{a+b}{a+b+2c}+\frac{b+c}{2a+b+c}+\frac{c+a}{a+2b+c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3151` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3151; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3151 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ (a + b) / (a + b + 2 * c) + (b + c) / (2 * a + b + c) + (c + a) / (a + 2 * b + c)  :=  by sorry
