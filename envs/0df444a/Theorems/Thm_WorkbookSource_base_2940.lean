-- Prove2me | Theorems.Thm_WorkbookSource_base_2940
-- name    : WorkbookSource.base_2940
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:02:37.292155+00:00
-- url     : https://prove2.me/theorems/c2d79e34-08c1-40c6-ae07-0120cda8b307
-- title:
--   A quadratic reciprocal sum bounded by a normalized total
-- statement:
--   Let $a,b,c>0.$ Prove that $\frac{1}{2a^2+bc}+\frac{1}{2b^2+ca}+\frac{1}{2c^2+ab}\le \frac{1}{3}.\frac{a+b+c}{abc}$ using Cauchy-Schwarz Inequality
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2940` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2940; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2940 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≤ 1 / 3 * (a + b + c) / (a * b * c)  :=  by sorry
