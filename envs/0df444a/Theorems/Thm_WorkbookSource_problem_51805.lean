-- Prove2me | Theorems.Thm_WorkbookSource_problem_51805
-- name    : WorkbookSource.problem_51805
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:04.72042+00:00
-- url     : https://prove2.me/theorems/dad6831c-fe0b-485a-a3cd-f2dbb3d9b3ed
-- title:
--   A cyclic sixth-degree square bound
-- statement:
--   By AM-GM inequality, $a^6+b^4c^2\geq 2a^3b^2c$ $\rightarrow$ $\sum_{cyc}a^6+\sum_{cyc}a^4b^2\geq 2\sum_{cyc}a^3b^2c$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51805` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51805; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_51805 (a b c : ℝ) : a^6 + b^6 + c^6 + a^4 * b^2 + b^4 * c^2 + c^4 * a^2 ≥ 2 * (a^3 * b^2 * c + b^3 * c^2 * a + c^3 * a^2 * b)  :=  by sorry
