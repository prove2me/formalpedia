-- Prove2me | Theorems.Thm_lean_workbook_plus_30240
-- name    : lean_workbook_plus_30240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/bc70e745-63a4-402a-bdd8-b076e2cd3b8a
-- statement:
--   Prove that if $ f(x)$ is a continuous function on $ [a, b]$ and $ f(a) \leq f(b)$, then there exists $ c \in [a, b]$ such that $ f(c) = f(a) + \frac{f(b) - f(a)}{b - a}(c - a)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30240 (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) (h : f a ≤ f b) : ∃ c ∈ Set.Icc a b, f c = f a + (f b - f a) / (b - a) * (c - a)   :=  by sorry
