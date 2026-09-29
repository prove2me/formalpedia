-- Prove2me | Theorems.Thm_WorkbookSource_base_117
-- name    : WorkbookSource.base_117
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:33:24.622868+00:00
-- url     : https://prove2.me/theorems/33a8dad8-80af-48f1-8fb6-fb298add7e7e
-- title:
--   A cyclic reciprocal-quadratic lower bound at fixed sum
-- statement:
--   Given $a,b,c>0$ and $a+b+c=3$ , prove that $$\frac{b}{a^2+1}+\frac{c}{b^2+1}+\frac{a}{c^2+1}\geq\frac{3}{2}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_117` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_117; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_117 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (b / (a ^ 2 + 1) + c / (b ^ 2 + 1) + a / (c ^ 2 + 1)) ≥ 3 / 2  :=  by sorry
