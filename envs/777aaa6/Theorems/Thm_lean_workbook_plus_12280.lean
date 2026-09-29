-- Prove2me | Theorems.Thm_lean_workbook_plus_12280
-- name    : lean_workbook_plus_12280
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/94d4b295-85d1-4534-bb64-1996fffeb4bf
-- statement:
--   Let $A(0,0)$ and $B(t,0)$ And point $P(p,0)$ where $0<p<t$ We want to consider $\frac{p}{t-p} <r$ Which is $p <rt-rp$ So $p<\frac{rt}{1+r}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12280 (p t r : ℝ) (h₀ : 0 < p ∧ 0 < t) (h₁ : p < t) (h₂ : 0 < r) : p / (t - p) < r ↔ p < (r * t) / (1 + r)   :=  by sorry
