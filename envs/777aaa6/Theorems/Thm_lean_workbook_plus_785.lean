-- Prove2me | Theorems.Thm_lean_workbook_plus_785
-- name    : lean_workbook_plus_785
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/914ec119-5b80-4ce4-921d-fde7e4a32009
-- statement:
--   The fact that $\gcd(a, p)=\gcd(b, p)$ does not imply $a=b$, but it does imply $a(a+p)=b(b+p)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_785  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < p)
  (h₁ : a ≠ b)
  (h₂ : Nat.gcd a p = Nat.gcd b p) :
  a * (a + p) = b * (b + p)   :=  by sorry
