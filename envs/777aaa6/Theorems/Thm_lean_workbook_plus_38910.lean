-- Prove2me | Theorems.Thm_lean_workbook_plus_38910
-- name    : lean_workbook_plus_38910
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e280a4e5-d9fb-4f54-91b8-18e550232712
-- statement:
--   For $ a\neq 0,\ b\neq 0,$ rewrite the expression in the form of $ a\sin \theta +b\cos \theta =\sqrt{a^2+b^2}\left(\sin \theta \cdot \frac{a}{\sqrt{a^2+b^2}}+\cos \theta \cdot \frac{b}{\sqrt{a^2+b^2}}\right).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38910 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a * sin θ + b * cos θ = Real.sqrt (a ^ 2 + b ^ 2) * (sin θ * a / Real.sqrt (a ^ 2 + b ^ 2) + cos θ * b / Real.sqrt (a ^ 2 + b ^ 2))   :=  by sorry
