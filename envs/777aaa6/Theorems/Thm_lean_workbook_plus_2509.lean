-- Prove2me | Theorems.Thm_lean_workbook_plus_2509
-- name    : lean_workbook_plus_2509
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/37c3a6a7-4e77-4e0a-9e67-e7a132c1edf4
-- statement:
--   Prove $ 12(a^4+b^4+c^4)\ge12(b^2c^2+c^2a^2-a^2b^2)$ where a,b,c are sides of a triangle using Muirhead's Theorem of Inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2509 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 12 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ 12 * (b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 - a ^ 2 * b ^ 2)   :=  by sorry
