-- Prove2me | Theorems.Thm_WorkbookSource_problem_32102
-- name    : WorkbookSource.problem_32102
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:59:05.680198+00:00
-- url     : https://prove2.me/theorems/e07904e5-64de-47f6-b9fd-900521385a9d
-- title:
--   Two bounds for a shifted three-factor product
-- statement:
--   Prove that for non-negative real numbers $x, y, z$ with $x + y + z = 1$, the following inequality holds:
--   $8 \leq (x + 1)(y + 2)(z + 3) \leq 12$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32102` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32102; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_32102 (x y z : ℝ) (hx : x + y + z = 1) (hx' : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) : 8 ≤ (x + 1) * (y + 2) * (z + 3) ∧ (x + 1) * (y + 2) * (z + 3) ≤ 12  :=  by sorry
