-- Prove2me | Theorems.Thm_lean_workbook_plus_27737
-- name    : lean_workbook_plus_27737
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/a68a0fa3-a039-417d-ba54-5fefa3195180
-- statement:
--   Write $a-b$ in base- $b$ representation. We have \n\n $${a-b}_{b}={\overline{k_nk_{n-1}\dots k_2k_1k_0}}_{b}\implies a-b=k_nb^n+k_{n-1}b^{n-1}+\cdots+k_1b+k_0$$ Keep in mind that $n\geq 1$ because $a-b\geq b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27737  (a b : ℕ)
  (h₁ : a ≥ b)
  (h₂ : 1 ≤ b)
  (h₃ : 0 < a - b) :
  ∃ (n : ℕ),
    ∃ (k : Fin (n + 1) → ℕ),
      a - b = ∑ i in Finset.range (n + 1), k i * b ^ i   :=  by sorry
