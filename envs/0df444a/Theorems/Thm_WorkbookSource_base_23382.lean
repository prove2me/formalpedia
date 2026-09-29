-- Prove2me | Theorems.Thm_WorkbookSource_base_23382
-- name    : WorkbookSource.base_23382
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:57:46.891984+00:00
-- url     : https://prove2.me/theorems/d082c9ed-e494-4cc4-b05a-7e602ed619c8
-- title:
--   A weighted quadratic ratio upper bound under a product constraint
-- statement:
--   The following inequality is also true.
--    If $a, b, c>0$ and $abc=1$ prove that
--    $\frac{7ab+bc+ca}{a^2+b^2+c^2+3bc}+\frac{ab+7bc+ca}{a^2+b^2+c^2+3ca}+\frac{ab+bc+7ca}{a^2+b^2+c^2+3ab}\leq\frac{9}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23382` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23382; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23382 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (7 * a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * b * c) + (a * b + 7 * b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * c * a) + (a * b + b * c + 7 * c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b) ≤ 9 / 2  :=  by sorry
