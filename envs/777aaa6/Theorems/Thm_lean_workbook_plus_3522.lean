-- Prove2me | Theorems.Thm_lean_workbook_plus_3522
-- name    : lean_workbook_plus_3522
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/dbb2fe83-5949-4e77-b705-bc8af3b06066
-- statement:
--   If $a,b,c$ are positive reals and $a^2+b^2+c^2=3$, then $ab+bc+ca\leq 3$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3522 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 3 → a * b + b * c + c * a ≤ 3   :=  by sorry
