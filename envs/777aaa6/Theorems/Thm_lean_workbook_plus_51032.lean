-- Prove2me | Theorems.Thm_lean_workbook_plus_51032
-- name    : lean_workbook_plus_51032
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/70584dce-a27f-48c1-985c-106f8d774340
-- statement:
--   For positive numbers a, b, c, d satisfy $ a> c $ , $ b> d $ . Prove that: $\sqrt{a+b} - \sqrt{c} - \sqrt{d} > \sqrt{c+d}- \sqrt{a} - \sqrt{b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51032 (a b c d : ℝ) (h₁ : a > c) (h₂ : b > d) (h₃ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) : Real.sqrt (a + b) - Real.sqrt c - Real.sqrt d > Real.sqrt (c + d) - Real.sqrt a - Real.sqrt b   :=  by sorry
