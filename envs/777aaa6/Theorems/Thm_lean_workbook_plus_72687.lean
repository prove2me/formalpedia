-- Prove2me | Theorems.Thm_lean_workbook_plus_72687
-- name    : lean_workbook_plus_72687
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/23437c2c-b851-4e99-8e2e-c8552bb23c05
-- statement:
--   For non-negative reals, we have $(a^3+b^3)^2=a^6+b^6+2a^3b^3\geqslant a^6+b^6$ and $(a+b)(a^5+b^5)=a^6+b^6+a^5b+ab^5\geqslant a^6+b^6$ ; with equality occuring in both cases if and only if $a=b=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72687 ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) : (a^3 + b^3)^2 ≥ a^6 + b^6 + 2 * a^3 * b^3   :=  by sorry
