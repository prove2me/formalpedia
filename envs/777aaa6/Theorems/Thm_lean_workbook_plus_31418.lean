-- Prove2me | Theorems.Thm_lean_workbook_plus_31418
-- name    : lean_workbook_plus_31418
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ce53e1af-3608-4044-91cb-55ba43e1772f
-- statement:
--   For this particular problem, $ 3 = \frac {s\sqrt {3}}{2}\quad\Longrightarrow\quad s = 2\sqrt {3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31418 (s : ℝ) : 3 = s * Real.sqrt 3 / 2 → s = 2 * Real.sqrt 3   :=  by sorry
