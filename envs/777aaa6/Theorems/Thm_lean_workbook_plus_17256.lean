-- Prove2me | Theorems.Thm_lean_workbook_plus_17256
-- name    : lean_workbook_plus_17256
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a5fe1cc3-4977-4606-bb12-2c3ae247d4b6
-- statement:
--   If $|2x-3| > 9$ , where $x$ is an integer, then $|x| > 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17256 : ∀ x : ℤ, ‖2 * x - 3‖ > 9 → ‖x‖ > 2   :=  by sorry
