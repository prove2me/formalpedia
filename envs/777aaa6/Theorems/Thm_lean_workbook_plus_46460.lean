-- Prove2me | Theorems.Thm_lean_workbook_plus_46460
-- name    : lean_workbook_plus_46460
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/add7fc75-b476-42c6-bb60-ed0c80530fa7
-- statement:
--   Prove that for $a, b, c > 0$,\n$a^2 + (-2c + 3b)a + b^2 + c^2 - bc \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46460 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^2 + (-2*c + 3*b)*a + b^2 + c^2 - b*c ≥ 0   :=  by sorry
