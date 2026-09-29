-- Prove2me | Theorems.Thm_lean_workbook_plus_16403
-- name    : lean_workbook_plus_16403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6d4fecad-f916-4f85-b12a-7d7fd6b041af
-- statement:
--   Suppose that $ f: \mathbb{R}\to \mathbb{R}$ is such that $ |f(x)-f(y)|\le c|x-y|$ for all $ x,y\in \mathbb{R}$ for some $ c>0$ . Prove that $ f$ is uniformly continuous. Can $ f$ be differentiable everywhere? Provide an example if not. Characterize the differentiability of $ f$ in terms of integrability.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16403 (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (h : ∀ x y, |f x - f y| ≤ c * |x - y|) : UniformContinuous f   :=  by sorry
