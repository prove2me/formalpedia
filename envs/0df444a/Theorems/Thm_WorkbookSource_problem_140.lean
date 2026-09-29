-- Prove2me | Theorems.Thm_WorkbookSource_problem_140
-- name    : WorkbookSource.problem_140
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:12.785322+00:00
-- url     : https://prove2.me/theorems/68b01430-c205-4b37-ad11-84bc961c0a3d
-- title:
--   Factoring a quadratic over the reals
-- statement:
--   Factor the expression $x^2 + 4x - 1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_140` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_140; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_140 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5)  :=  by sorry
