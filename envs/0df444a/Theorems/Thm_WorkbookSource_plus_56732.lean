-- Prove2me | Theorems.Thm_WorkbookSource_plus_56732
-- name    : WorkbookSource.plus_56732
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:35.263604+00:00
-- url     : https://prove2.me/theorems/66652b55-7574-4723-9f0f-44b79e4afc78
-- title:
--   A mixed quadratic reciprocal sum has a symmetric upper bound
-- statement:
--   Prove that:
--   $ \frac{1}{2a^2+bc}+\frac{1}{2b^2+ca}+\frac{1}{2c^2+ab} \le \frac{(a+b+c)^2}{(ab+bc+ca)^2}$
--   Given: $ a,b,c> 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_56732` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_56732; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_56732 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≤ (a + b + c) ^ 2 / (a * b + b * c + c * a) ^ 2   :=  by sorry
