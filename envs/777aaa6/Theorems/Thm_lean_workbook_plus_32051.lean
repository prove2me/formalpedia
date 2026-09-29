-- Prove2me | Theorems.Thm_lean_workbook_plus_32051
-- name    : lean_workbook_plus_32051
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0ba3d464-4109-4d91-8de2-7c3b44756cc2
-- statement:
--   Prove that for positive real numbers $a, b, c, d, e, f$, the following inequality holds:\n${\frac{ab}{a+b}+\frac{cd}{c+d}+\frac{ef}{e+f}\le \frac{(a+c+e)(b+d+f)}{a+b+c+d+e+f}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32051 ∀ a b c d e f : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0 ∧ f > 0 → (a * b / (a + b) + c * d / (c + d) + e * f / (e + f) : ℝ) ≤ (a + c + e) * (b + d + f) / (a + b + c + d + e + f)   :=  by sorry
