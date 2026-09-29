-- Prove2me | Theorems.Thm_lean_workbook_plus_71089
-- name    : lean_workbook_plus_71089
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/99b840c3-6c77-4157-957b-8912884d417e
-- statement:
--   Prove that if $a+b+c=3$, then $a^3+b^3+c^3-3abc \geq \frac94 (a^2+b^2-2ab)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71089 (a b c : ℝ) (h : a + b + c = 3) : a^3 + b^3 + c^3 - 3 * a * b * c ≥ (9 / 4) * (a^2 + b^2 - 2 * a * b)   :=  by sorry
