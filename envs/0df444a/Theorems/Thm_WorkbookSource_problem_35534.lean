-- Prove2me | Theorems.Thm_WorkbookSource_problem_35534
-- name    : WorkbookSource.problem_35534
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:55.764544+00:00
-- url     : https://prove2.me/theorems/6ef0a86a-dd9b-4436-9fb9-a8b0597096cd
-- title:
--   A simple exact multiple of pi
-- statement:
--   The following exact value holds:
--
--   $$\frac\pi2(1+1)=\pi.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35534` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35534; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_35534 (h₁ : π / 2 * 1 = π / 2) : π / 2 * (1 + 1) = π  :=  by sorry
