-- Prove2me | Theorems.Thm_WorkbookSource_plus_5958
-- name    : WorkbookSource.plus_5958
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:41:27.019533+00:00
-- url     : https://prove2.me/theorems/ef28092b-89eb-4b3f-8f76-fd98be46d30e
-- title:
--   A sharp square-sum bound under a mixed constraint
-- statement:
--   Given $a + b^2 + c^2 = 4$ , prove that
--    $$a^2 + b^2 + c^2 \ge \frac{15}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_5958` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_5958; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_5958 (a b c : ℝ) (h : a + b^2 + c^2 = 4) : a^2 + b^2 + c^2 ≥ 15 / 4   :=  by sorry
