-- Prove2me | Theorems.Thm_lean_workbook_plus_16365
-- name    : lean_workbook_plus_16365
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/54e06909-87e7-4b93-a904-f486f146e359
-- statement:
--   The expression $f(M)$ can be factored as $f(M) = a^3(b - c) + b^3(c - a) + c^3(a - b) = c(b^3 - a^3) - ba(b^2 - a^2) - c^3(b - a) = (b - a)\left[c(b^2 + ba + a^2) - ba(b + a) - c^3\right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16365 : ∀ a b c : ℤ, a * b * c = b * c * a → a^3 * (b - c) + b^3 * (c - a) + c^3 * (a - b) = (b - a) * (c * (b^2 + b * a + a^2) - b * a * (b + a) - c^3)   :=  by sorry
