-- Prove2me | Theorems.Thm_WorkbookSource_problem_36537
-- name    : WorkbookSource.problem_36537
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:20.430479+00:00
-- url     : https://prove2.me/theorems/c428fe15-e3d9-437f-99f4-c8638cd27811
-- title:
--   A trigonometric consequence of a square inequality
-- statement:
--   For real angles $\beta,\theta$, if $(\sin\beta+\cos\theta+1)^2\ge2(\sin\beta+1)(\cos\theta+1)$, then $\sin^2\beta\ge\sin^2\theta$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36537` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Related existing records plus_81151, plus_49334 and plus_5885 omit the angle declarations; this record uses the original source’s explicit real variables.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36537; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_36537 (β θ : ℝ) : (sin β + cos θ + 1)^2 ≥ 2 * (sin β + 1) * (cos θ + 1) → sin β ^ 2 ≥ sin θ ^ 2  :=  by sorry
