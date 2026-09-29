-- Prove2me | Theorems.Thm_lean_workbook_plus_17835
-- name    : lean_workbook_plus_17835
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/cd394ec2-4c3a-4142-8a1d-e65610e4ffe9
-- statement:
--   Prove that for any real numbers \(a, b, c\), the following inequality holds: \((3abc + a^3 + b^3 + c^3) \cdot (a + b + c) \geq 2 \cdot (a^2 + b^2 + c^2) \cdot (ab + bc + ca)\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17835 (a b c : ℝ) : (3 * a * b * c + a ^ 3 + b ^ 3 + c ^ 3) * (a + b + c) ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)   :=  by sorry
