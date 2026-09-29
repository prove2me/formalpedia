-- Prove2me | Theorems.Thm_lean_workbook_plus_14972
-- name    : lean_workbook_plus_14972
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/03bf1b38-527a-467c-ac6c-68e139225082
-- statement:
--   Since $|z|<\frac{1}{2}$, we have $2|z|^2\leq |z|^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14972 : ∀ z : ℂ, ‖z‖ < 1 / 2 → 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2   :=  by sorry
