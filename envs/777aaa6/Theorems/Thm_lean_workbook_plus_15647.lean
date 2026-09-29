-- Prove2me | Theorems.Thm_lean_workbook_plus_15647
-- name    : lean_workbook_plus_15647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/58f085c7-f6d5-45d4-932c-a66746aa8300
-- statement:
--   Prove that if $ a\leq b\leq c\leq d$ and $ b+c=a+d\Rightarrow bc\geq ad$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15647 (a b c d : ℝ) (h1: a ≤ b ∧ b ≤ c ∧ c ≤ d) (h2: b + c = a + d) : b * c ≥ a * d   :=  by sorry
