-- Prove2me | Theorems.Thm_lean_workbook_plus_66680
-- name    : lean_workbook_plus_66680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/2c62445a-8f9d-43b0-8f62-94687259b0fa
-- statement:
--   If $f(0) = 0$ , then $f(x)^3 = f(x)^2$ , so $f(x) = 0$ or $f(x) = 1$ for any $x$ . Also, the statement in the problem becomes $f(x)+f(y) = f(x+y)$ . Suppose $f(a) = 1$ for some $a$ , then $f(2a) = f(a) + f(a) = 1+1 = 2$ , contradiction. So $f(x) = 0$ for all $x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66680  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 0 ∨ ∀ x, f x = 1)
  (h₁ : ∀ x y, f (x + y) = f x + f y)
  (h₂ : f 0 = 0) :
  ∀ x, f x = 0   :=  by sorry
