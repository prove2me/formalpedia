-- Prove2me | Theorems.Thm_lean_workbook_plus_61984
-- name    : lean_workbook_plus_61984
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/428e4425-cb4a-42c7-b5b2-19102aa0e503
-- statement:
--   Prove that for non-negative numbers $a, b, c, d, e, f$, the following identity holds: \(-(ad+be+cf)^2 + 3/4a^2d(d+a) + 3/4b^2e(b+e) + 3/4c^2f(c+f) + 3/4d^2a(d+a) + 3/4e^2b(b+e) + 3/4f^2c(c+f) = 3/8(f-c)^2cf + 3/8(d-a)^2ad + 3/8(e-b)^2be + 3/8(b-e)^2be + 3/8(c-f)^2cf + 3/8(a-d)^2ad + 1/3(2ad-be-cf)^2 + 1/3(2be-ad-cf)^2 + 1/3(2cf-ad-be)^2\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61984 : ∀ a b c d e f : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 → -(ad+be+cf)^2 + 3/4*a^2*d*(d+a) + 3/4*b^2*e*(b+e) + 3/4*c^2*f*(c+f) + 3/4*d^2*a*(d+a) + 3/4*e^2*b*(b+e) + 3/4*f^2*c*(c+f) = 3/8*(f-c)^2*c*f + 3/8*(d-a)^2*a*d + 3/8*(e-b)^2*b*e + 3/8*(b-e)^2*b*e + 3/8*(c-f)^2*c*f + 3/8*(a-d)^2*a*d + 1/3*(2*a*d-b*e-c*f)^2 + 1/3*(2*b*e-a*d-c*f)^2 + 1/3*(2*c*f-a*d-b*e)^2   :=  by sorry
