-- Prove2me | Theorems.Thm_lean_workbook_plus_20489
-- name    : lean_workbook_plus_20489
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/2f81022c-106c-48fe-be77-8438a880f17c
-- statement:
--   Given the definition of limit: $ \lim_{x\rightarrow a} f(x)=F$ if for every positive $ \epsilon$ , there exists a positive $ \delta$ such that if $ x\neq a$ and $ |x-a|<\delta$ , then $ |f(x)-F|<\epsilon$ . Prove that $ \lim_{x \to a} f(x) + g(x) = F + G$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20489 (f g : ℝ → ℝ) (a F G : ℝ) (hf : ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ a ∧ |x - a| < δ → |f x - F| < ε) (hg : ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ a ∧ |x - a| < δ → |g x - G| < ε) : ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ a ∧ |x - a| < δ → |f x + g x - (F + G)| < ε   :=  by sorry
