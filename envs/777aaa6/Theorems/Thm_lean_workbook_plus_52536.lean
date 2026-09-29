-- Prove2me | Theorems.Thm_lean_workbook_plus_52536
-- name    : lean_workbook_plus_52536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/0f8a2113-2263-4a44-abce-2816b77e7dea
-- statement:
--   Square both sides of the inequality $a^2b^2c^2 \geq |(a^2 - b^2)(b^2 - c^2)(c^2 - a^2)|$ to obtain $a^4b^4c^4 \geq (a^2 - b^2)^2(b^2 - c^2)^2(c^2 - a^2)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52536 :  ∀ a b c : ℝ, a^2 * b^2 * c^2 ≥ |(a^2 - b^2) * (b^2 - c^2) * (c^2 - a^2)| → a^4 * b^4 * c^4 ≥ (a^2 - b^2)^2 * (b^2 - c^2)^2 * (c^2 - a^2)^2   :=  by sorry
