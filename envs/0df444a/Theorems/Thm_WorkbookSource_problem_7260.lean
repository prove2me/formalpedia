-- Prove2me | Theorems.Thm_WorkbookSource_problem_7260
-- name    : WorkbookSource.problem_7260
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:45:56.227085+00:00
-- url     : https://prove2.me/theorems/c742d3c1-51c2-40dd-9436-f8b2a0dcb045
-- title:
--   Evaluating a composition at opposite inputs
-- statement:
--   Let $f(x) = 3x^2-7$ and $g(f(4)) = 9$ . What is $g(f(-4))$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7260` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7260; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_7260 (f g : ℝ → ℝ) (hf : ∀ x, f x = 3 * x ^ 2 - 7) (hg : g (f 4) = 9) : g (f (-4)) = 9  :=  by sorry
