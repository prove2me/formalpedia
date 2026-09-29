-- Prove2me | Theorems.Thm_WorkbookSource_problem_53396
-- name    : WorkbookSource.problem_53396
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:51.102405+00:00
-- url     : https://prove2.me/theorems/4a5af354-066b-4471-9e26-a40fc5f2dc82
-- title:
--   Subadditivity of a truncated sum
-- statement:
--   Let $a\geq 0,\ b\geq 0,\ c\geq 0$ . Prove that $\min\{a+b,\ c\}\leq \min\{a,\ c\}+\min\{b,\ c\}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53396` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53396; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_53396 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : min (a + b) c ≤ min a c + min b c  :=  by sorry
