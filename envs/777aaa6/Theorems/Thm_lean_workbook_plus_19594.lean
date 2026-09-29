-- Prove2me | Theorems.Thm_lean_workbook_plus_19594
-- name    : lean_workbook_plus_19594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d487ff31-bb0f-45ea-b6be-566ab88e0f5d
-- statement:
--   We have this by Cauchy Schwarz: $2(a^2+b^2)(b^2+c^2)(c^2+a^2)=[(a-b)^2+(a+b)^2][c^2(a-b)^2+(c^2+ab)^2] \geq [c(a-b)^2+(c^2+ab)(a+b)]^2=[(a+b)(b+c)(c+a)-4abc]^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19594 : ∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) ≥ ((a + b) * (b + c) * (c + a) - 4 * a * b * c) ^ 2   :=  by sorry
