-- Prove2me | Theorems.Thm_lean_workbook_plus_58004
-- name    : lean_workbook_plus_58004
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/ab87d88b-38cb-4bc5-b1f3-34401493262c
-- statement:
--   Let's look at the squares of non-zero elements. If $x^2=a$ , then $(-x)^2=a$ , and $x\ne -x$ for all non-zero $x$ . This means that the only way we can have $\frac {n-1}2$ non-zero squares is if $x^2=y^2$ implies $x=y$ or $x=-y$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58004  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∀ x : ZMod n, x ≠ 0 → ∃! y, y^2 = x^2) :
  ∀ x : ZMod n, x ≠ 0 → ∀ y : ZMod n, y ≠ 0 → x^2 = y^2 → x = y ∨ x = -y   :=  by sorry
