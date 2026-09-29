-- Prove2me | Theorems.Thm_lean_workbook_plus_13156
-- name    : lean_workbook_plus_13156
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/58512478-01ea-4e74-a252-e49bb736e74a
-- statement:
--   Let $a,\ b,\ c$ and $d$ be positive real numbers such that $a^2+b^2=c^2+d^2=1.$ Prove that $\frac{b}{a}+\frac{d}{c}\geq 2\frac{b+d}{a+c}.$ Proposed by A certain Japanese High School Student
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13156 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a^2 + b^2 = 1) (hcd : c^2 + d^2 = 1) : b / a + d / c ≥ 2 * (b + d) / (a + c)   :=  by sorry
