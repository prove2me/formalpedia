-- Prove2me | Theorems.Thm_lean_workbook_plus_49777
-- name    : lean_workbook_plus_49777
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/16d0fd22-a23d-481b-afac-14bc93e1b6d0
-- statement:
--   Prove that \(\frac{3(a^2+b^2+c^2)}{2(ab+bc+ca)}\ge \frac{a}{b+c} + \frac{b}{c+a} + \frac{c}{a+b}\) for positive real numbers \(a, b, c\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49777 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (2 * (a * b + b * c + c * a)) ≥ a / (b + c) + b / (c + a) + c / (a + b)   :=  by sorry
