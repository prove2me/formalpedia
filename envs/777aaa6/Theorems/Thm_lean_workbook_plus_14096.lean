-- Prove2me | Theorems.Thm_lean_workbook_plus_14096
-- name    : lean_workbook_plus_14096
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/117928f5-5d3f-4002-a37a-35b118007ca7
-- statement:
--   Denote $\frac{y}{x}=a$ , $\frac{z}{y}=b$ , $\frac{t}{z}=c$ , $\frac{x}{t}=d$ so we have $abcd=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14096 (x y z t a b c d : ℝ) (h₁ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ t ≠ 0) (h₂ : a = y / x ∧ b = z / y ∧ c = t / z ∧ d = x / t) : a * b * c * d = 1   :=  by sorry
