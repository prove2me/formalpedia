-- Prove2me | Theorems.Thm_lean_workbook_plus_46871
-- name    : lean_workbook_plus_46871
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ad6fd7ac-9bd0-42ea-9da9-ed361ba5176f
-- statement:
--   prove that $\frac{a^7+b^7+c^7}{7}=\frac{a^5+b^5+c^5}{5}\cdot\frac{a^2+b^2+c^2}{2}$ if $a+b+c=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46871 : ∀ a b c : ℝ, a + b + c = 0 → (a^7 + b^7 + c^7) / 7 = (a^5 + b^5 + c^5) / 5 * (a^2 + b^2 + c^2) / 2   :=  by sorry
