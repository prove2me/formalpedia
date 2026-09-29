-- Prove2me | Theorems.Thm_lean_workbook_plus_72595
-- name    : lean_workbook_plus_72595
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f51fb2cc-0c09-4094-b8d9-18886ed1d59e
-- statement:
--   Let $LHS=8a^3+3b^3+3c^3+b^2c+bc^2-4(a^2b+ab^2+a^2c+ac^2)$ . We want to show that $LHS\ge 0$ for $a,b,c>0.$ Rearranging terms we get $LHS=4(2a+b+c)(a-b)(a-c)+3(b+c)(b-c)^2$ . Clearly $LHS\ge 0$ when $a\ge b,c$ or $a\le b,c$ . Because $LHS$ is symmetric in $b,c$ , all we have to examine now is the case $b\le a\le c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72595  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : b ≤ a ∧ a ≤ c) :
  8 * a^3 + 3 * b^3 + 3 * c^3 + b^2 * c + b * c^2 - 4 * (a^2 * b + a * b^2 + a^2 * c + a * c^2) ≥ 0   :=  by sorry
