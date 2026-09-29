-- Prove2me | Theorems.Thm_lean_workbook_plus_80420
-- name    : lean_workbook_plus_80420
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7fb590b4-9377-4e4e-a0e7-9993986dc276
-- statement:
--   Prove that if \\(\\frac{m}{n}=\\frac11+\\frac12+\\dots+\\frac{1}{p-1}\\) where \\(p\\) is a odd prime, then \\(p|m\\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80420 {p m n : ℕ} (hp : p.Prime) (hp1 : Odd p) : (m : ℚ) / n = ∑ k in Finset.range p, 1 / (k + 1) → (p : ℚ) ∣ m   :=  by sorry
