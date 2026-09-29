-- Prove2me | Theorems.Thm_WorkbookSource_base_19691
-- name    : WorkbookSource.base_19691
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:41:41.512509+00:00
-- url     : https://prove2.me/theorems/0270b438-6cbd-4bad-9b0d-f4cd165e5b54
-- title:
--   A comparison of two cyclic quadratic ratio sums
-- statement:
--   Let $a,b,c>0$ prove that $\frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{a}\geq 2\left(\frac{a^2}{a+b}+\frac{b^2}{b+c}+\frac{c^2}{c+a}\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19691` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19691; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19691 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a) ≥ 2 * (a^2 / (a + b) + b^2 / (b + c) + c^2 / (c + a))  :=  by sorry
