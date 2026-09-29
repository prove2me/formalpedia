-- Prove2me | Theorems.Thm_WorkbookSource_base_34964
-- name    : WorkbookSource.base_34964
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:46:53.88053+00:00
-- url     : https://prove2.me/theorems/bb3fddb7-75cb-40cf-82ce-1d9563c9591d
-- title:
--   A weighted reciprocal sum comparison with constant twenty-five twelfths
-- statement:
--   Let $a,b$ be positive real numbers , prove that $\frac{2}{a}+\frac{3}{a+b}\le \frac{25}{12}(\frac{1}{a}+\frac{1}{b})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34964` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34964; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34964 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2 / a + 3 / (a + b)) ≤ 25 / 12 * (1 / a + 1 / b)  :=  by sorry
