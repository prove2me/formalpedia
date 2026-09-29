-- Prove2me | Theorems.Thm_lean_workbook_plus_5599
-- name    : lean_workbook_plus_5599
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/ed66ed6c-e162-46a4-9539-bea31eff8ea9
-- statement:
--   By use Fermat last theorem there is no three integers $a,b,c$ satisfy the equation $a^n+b^n=c^n$ for $n>2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5599 : ¬ ∃ (a b c : ℤ) (n : ℕ), n > 2 ∧ a^n + b^n = c^n   :=  by sorry
