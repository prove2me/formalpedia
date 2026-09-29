-- Prove2me | Theorems.Thm_WorkbookSource_problem_8823
-- name    : WorkbookSource.problem_8823
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:21.924695+00:00
-- url     : https://prove2.me/theorems/3f92c63e-30ad-41fa-a1b3-690f562d34a0
-- title:
--   Two equivalent formulations of a cubic mean inequality
-- statement:
--   $ 4(a^3 + b^3)\geq (a + b)^3\Longleftrightarrow \frac{a^3+b^3}{2}\geq \left(\frac{a+b}{2}\right)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8823` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8823; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_8823 (a b : ℝ) : 4 * (a ^ 3 + b ^ 3) ≥ (a + b) ^ 3 ↔ (a ^ 3 + b ^ 3) / 2 ≥ ((a + b) / 2) ^ 3  :=  by sorry
