-- Prove2me | Theorems.Thm_lean_workbook_plus_62330
-- name    : lean_workbook_plus_62330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/947998db-ce6c-48bc-902d-bf39e89a0631
-- statement:
--   Denote $p(x)$ to be the probability of no consecutive tails after $x$ coin flips. When $x\ge 2$ , $p(x)=\frac{1}{2}p(x-1)+\frac{1}{2}\times\frac{1}{2}p(x-2)$ . Now we can build a chart and get to $6$ coin flips. $p(0)=1, p(1)=1, p(2)=\frac{1}{2}\times1+\frac{1}{4}\times1=\frac{3}{4}, p(3)=\frac{5}{8}, p(4)=\frac{8}{16}, p(5)=\frac{13}{32}, p(6)=\frac{21}{64}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62330  (p : ℕ → ℚ)
  (h₀ : p 0 = 1)
  (h₁ : p 1 = 1)
  (h₂ : ∀ x, p (x + 2) = 1 / 2 * p (x + 1) + 1 / 4 * p x) :
  p 6 = 21 / 64   :=  by sorry
