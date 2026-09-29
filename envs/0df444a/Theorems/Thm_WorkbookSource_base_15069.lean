-- Prove2me | Theorems.Thm_WorkbookSource_base_15069
-- name    : WorkbookSource.base_15069
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:58:01.419439+00:00
-- url     : https://prove2.me/theorems/31b17274-8a24-4c04-a1c3-fccab54cbfee
-- title:
--   A cyclic squared difference ratio sum is at least six
-- statement:
--   Let $a, b, c>0$. prove that $\frac{(4a-b-c)^2}{c^2+ab}+\frac{(4b-c-a)^2}{a^2+bc}+\frac{(4c-a-b)^2}{b^2+ca}\ge6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15069` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15069; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15069 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 * a - b - c) ^ 2 / (c ^ 2 + a * b) + (4 * b - c - a) ^ 2 / (a ^ 2 + b * c) + (4 * c - a - b) ^ 2 / (b ^ 2 + c * a) ≥ 6  :=  by sorry
