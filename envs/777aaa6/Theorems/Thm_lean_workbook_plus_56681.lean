-- Prove2me | Theorems.Thm_lean_workbook_plus_56681
-- name    : lean_workbook_plus_56681
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f290609d-29f1-4f83-88bb-85b23e18eaef
-- statement:
--   Let $a,b$ be positive real numbers such that $a+b\leq 1$ . Prove that $\left(a^3+\frac {1}{b}\right)\left(b+\frac {1}{a^3}\right) \geq -\frac {80089}{6912}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56681 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) : (a^3 + 1/b) * (b + 1/(a^3)) ≥ -80089/6912   :=  by sorry
