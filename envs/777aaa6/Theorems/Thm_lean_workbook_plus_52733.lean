-- Prove2me | Theorems.Thm_lean_workbook_plus_52733
-- name    : lean_workbook_plus_52733
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9049a2e0-15ae-4ad2-833f-87767433096b
-- statement:
--   and $\frac{2+abc}{1+abc}+abc \le \frac{5}{2} \iff (1+2abc)(1-abc) \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52733 : ∀ a b c : ℝ, (2 + a * b * c) / (1 + a * b * c) + a * b * c ≤ 5 / 2 ↔ (1 + 2 * a * b * c) * (1 - a * b * c) ≥ 0   :=  by sorry
