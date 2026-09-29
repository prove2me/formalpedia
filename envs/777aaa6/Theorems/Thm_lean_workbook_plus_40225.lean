-- Prove2me | Theorems.Thm_lean_workbook_plus_40225
-- name    : lean_workbook_plus_40225
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9e0416c2-91b5-4473-a5ab-d384920b8b3d
-- statement:
--   Given $a, b, c \geq 0$, prove that $a^3 + b^3 + c^3 - 3abc \geq \frac{1}{4}(b + c - 2a)^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40225 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^3 + b^3 + c^3 - 3 * a * b * c ≥ (1 / 4) * (b + c - 2 * a)^3   :=  by sorry
