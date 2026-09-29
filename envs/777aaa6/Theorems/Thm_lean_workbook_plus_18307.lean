-- Prove2me | Theorems.Thm_lean_workbook_plus_18307
-- name    : lean_workbook_plus_18307
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6f9cba67-a125-47e1-a56a-71a78b9ffc59
-- statement:
--   Prove that \(\frac{ab+k}{a+b}+\frac{bc+k}{b+c}+\frac{ca+k}{c+a}\leq \frac{k-7}{2}\) where \(a,b,c\) are non-negative reals such that \(ab + bc + ca = 1\) and \(k > 0\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18307 : ∀ a b c k : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a * b + b * c + c * a = 1 ∧ k > 0 → (a * b + k) / (a + b) + (b * c + k) / (b + c) + (c * a + k) / (c + a) ≤ (k - 7) / 2   :=  by sorry
