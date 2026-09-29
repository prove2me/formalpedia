-- Prove2me | Theorems.Thm_lean_workbook_plus_65567
-- name    : lean_workbook_plus_65567
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0a71d444-1c4a-4f2e-bf05-d1ff596d6299
-- statement:
--   The probability of same-color-ness is $ \dfrac {4}{10} \cdot \dfrac {16}{16 + N} + \dfrac {6}{10} \cdot \dfrac {N}{16+N} = \dfrac {29}{50}. $ This is a simple linear equation. We get $N=\boxed{144}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65567  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : (4:ℝ) / 10 * (16:ℝ) / (16 + n) + 6 / 10 * n / (16 + n) = 29 / 50) :
  n = 144   :=  by sorry
