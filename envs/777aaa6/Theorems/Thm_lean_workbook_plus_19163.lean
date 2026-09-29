-- Prove2me | Theorems.Thm_lean_workbook_plus_19163
-- name    : lean_workbook_plus_19163
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d4eab463-c6a2-49a8-bd9a-cd8ae76e9f14
-- statement:
--   2) Let $a>0$ and $t\ge 0$ , then : $g(x)=x^t$ $\forall x>0$ $g(0)=0$ $g(x)=-a(-x)^t$ $\forall x<0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19163 (a t : ℝ) (ha : a > 0) (ht : t ≥ 0) : ∃ g : ℝ → ℝ, ∀ x > 0, g x = x ^ t ∧ g 0 = 0 ∧ ∀ x < 0, g x = -a * (-x) ^ t   :=  by sorry
