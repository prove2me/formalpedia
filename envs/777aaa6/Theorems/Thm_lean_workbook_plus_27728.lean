-- Prove2me | Theorems.Thm_lean_workbook_plus_27728
-- name    : lean_workbook_plus_27728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d439f16b-0934-43be-a964-6b958cd1a223
-- statement:
--   Let $a\in\mathbb{R}$ and let $f,g,h$ be real-valued functions such that $f(x)\le g(x)\le h(x)$ for all $x$ in an open interval containing $a$ (but not necessarily at $a$ itself). If $\lim_{x\to a}f(x)=\lim_{x\to a}h(x)=L$, then $\lim_{x\to a}g(x)=L$ as well.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27728 (a : ℝ) (f g h : ℝ → ℝ) (hf : ∀ x, f x ≤ g x) (hg : ∀ x, g x ≤ h x) (h1 : ContinuousAt f a) (h2 : ContinuousAt h a) (h3 : f a = h a) : ContinuousAt g a   :=  by sorry
