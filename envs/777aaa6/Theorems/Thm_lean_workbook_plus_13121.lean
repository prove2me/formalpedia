-- Prove2me | Theorems.Thm_lean_workbook_plus_13121
-- name    : lean_workbook_plus_13121
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/ee8f03b3-a0a7-4955-ac75-cfcec1dc6679
-- statement:
--   Prove that if $f$ is continuous on $\mathbb{R}$ and $(\forall x \in \mathbb{R}): f(x)^2 = x^2$, then $(\forall x \in \mathbb{R}): f(x) = x$ or $(\forall x \in \mathbb{R}): f(x) = -x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13121  ∀ f : ℝ → ℝ, (∀ x, f x ^ 2 = x ^ 2) ∧ Continuous f →  (∀ x, f x = x) ∨ (∀ x, f x = -x)   :=  by sorry
