-- Prove2me | Theorems.Thm_lean_workbook_plus_42708
-- name    : lean_workbook_plus_42708
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/09ab33ea-1e74-4b89-a144-6eb2b0d4ef05
-- statement:
--   Let $a,b,c\geq 0$ . Prove that \n\n $$a^2+2b^2+c^2 \ge \frac{2\sqrt{3}}{3}(a+2b)c$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42708 : ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a^2 + 2 * b^2 + c^2 ≥ (2 * Real.sqrt 3) / 3 * (a + 2 * b) * c   :=  by sorry
