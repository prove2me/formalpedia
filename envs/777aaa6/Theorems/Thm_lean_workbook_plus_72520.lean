-- Prove2me | Theorems.Thm_lean_workbook_plus_72520
-- name    : lean_workbook_plus_72520
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/91043c45-ba31-439b-9f77-059f6d50477d
-- statement:
--   Let $r$ be a (not necessarily real) root of $Q(x)-1=0$ . Substituting $x=r$ gives\n\n P(1)=0\nTherefore, $1$ is a root of $P$ . We have $P(1)=a+b+c\implies c=-a-b$ . This gives us:\n\n P(x)=ax^2+bx-a-b=(x-1)(ax+a+b)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72520  (a b c : ℂ)
  (f : ℂ → ℂ)
  (h₀ : ∀ x, f x = a * x^2 + b * x + c)
  (h₁ : f 1 = 0) :
  c = -a - b   :=  by sorry
