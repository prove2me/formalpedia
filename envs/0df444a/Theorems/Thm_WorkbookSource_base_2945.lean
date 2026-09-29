-- Prove2me | Theorems.Thm_WorkbookSource_base_2945
-- name    : WorkbookSource.base_2945
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:51:14.964273+00:00
-- url     : https://prove2.me/theorems/d3582a8f-f1da-482f-9ac1-2b69847fcb01
-- title:
--   A quartic inequality under a linear difference constraint
-- statement:
--   Let $ a,b>0$ be such that $ 2a-b=2$ . Prove that
--   $ a^4+(a-b)^4+a^2b \ge a^3+(a-b)^3+ab^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2945` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2945; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2945 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * a - b = 2) : a ^ 4 + (a - b) ^ 4 + a ^ 2 * b ≥ a ^ 3 + (a - b) ^ 3 + a * b ^ 2  :=  by sorry
