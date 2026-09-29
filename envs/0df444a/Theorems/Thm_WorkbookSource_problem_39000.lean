-- Prove2me | Theorems.Thm_WorkbookSource_problem_39000
-- name    : WorkbookSource.problem_39000
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:39:49.842748+00:00
-- url     : https://prove2.me/theorems/745f86d0-502e-4225-9c06-76a550a9596d
-- title:
--   Expanding a product lower bound
-- statement:
--   For real numbers $y,z$ with $(y-1)(z-1)\ge0$,
--
--   $$yz\ge y+z-1.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39000` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39000; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_39000  (y z : ℝ)
  (h₀ : (y - 1) * (z - 1) ≥ 0) :
  y * z ≥ y + z - 1  :=  by sorry
