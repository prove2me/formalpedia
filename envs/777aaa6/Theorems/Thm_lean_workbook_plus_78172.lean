-- Prove2me | Theorems.Thm_lean_workbook_plus_78172
-- name    : lean_workbook_plus_78172
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/87cb13e0-6722-4048-b27e-88f8954bafc3
-- statement:
--   Let $\lfloor \sqrt{n} \rfloor =m$ Thus $n=m^2+k$ with $0\leq k\leq 2m$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78172 (n : ℕ) (m k : ℕ) (h₁ : 0 ≤ k) (h₂ : k ≤ 2 * m) (h₃ : n = m^2 + k) : ⌊Real.sqrt n⌋ = m   :=  by sorry
