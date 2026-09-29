-- Prove2me | Theorems.Thm_WorkbookSource_problem_48161
-- name    : WorkbookSource.problem_48161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:10:16.050738+00:00
-- url     : https://prove2.me/theorems/ded653d5-7a7a-46f7-80e7-7f8dd9d17676
-- title:
--   Solving a four-equation linear system
-- statement:
--   Solve the system: $x - y + z-t=1$, $8x -4 y + 2z-t=16$, $27x -9y+ 3z-t=81$, $64x-16y+4z-t=256$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48161` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_48161 (x y z t : ℝ) : x - y + z - t = 1 ∧ 8 * x - 4 * y + 2 * z - t = 16 ∧ 27 * x - 9 * y + 3 * z - t = 81 ∧ 64 * x - 16 * y + 4 * z - t = 256 ↔ x = 10 ∧ y = 35 ∧ z = 50 ∧ t = 24  :=  by sorry
