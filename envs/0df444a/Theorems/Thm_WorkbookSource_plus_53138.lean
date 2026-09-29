-- Prove2me | Theorems.Thm_WorkbookSource_plus_53138
-- name    : WorkbookSource.plus_53138
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:56.77069+00:00
-- url     : https://prove2.me/theorems/c0062c13-854b-4bc0-b0a9-bef520ef82f2
-- title:
--   A refined reciprocal product inequality with a quadratic correction
-- statement:
--   prove that $6(\frac{1}{a}+\frac{1}{b}+\frac{1}{c})(a+b+c)^{3}+3(ab+bc+ca)\geq55(a+b+c)^{2}$ with $a;b;c>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_53138` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_53138; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_53138 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  6 * (1 / a + 1 / b + 1 / c) * (a + b + c) ^ 3 + 3 * (a * b + b * c + c * a) ≥ 55 * (a + b + c) ^ 2   :=  by sorry
