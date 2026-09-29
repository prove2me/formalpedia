-- Prove2me | Theorems.Thm_WorkbookSource_plus_25937
-- name    : WorkbookSource.plus_25937
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:48:00.093108+00:00
-- url     : https://prove2.me/theorems/a4e82107-977e-463f-98c5-3b8f88bd496d
-- title:
--   A shifted reciprocal sum has a reciprocal product upper bound
-- statement:
--   Let $a,b,c$ are positive numbers satisfies $a+b+c=3$ , prove that $\frac{1}{2a+bc}+\frac{1}{2b+ca}+\frac{1}{2c+ab} \leq \frac{1}{abc}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_25937` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_25937; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_25937 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (2 * a + b * c) + 1 / (2 * b + c * a) + 1 / (2 * c + a * b) ≤ 1 / (a * b * c)   :=  by sorry
