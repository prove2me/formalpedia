-- Prove2me | Theorems.Thm_lean_workbook_plus_62677
-- name    : lean_workbook_plus_62677
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/1b6b22de-77a8-453b-a14e-56d2e27aa10e
-- statement:
--   If $Q(x) = \left(x + \frac{1}{2}\right)^2 + \frac{8003}{4}$, show that $Q(x) \geq \frac{8003}{4}$ for all $x \in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62677 (x: ℝ) (Q: ℝ → ℝ) (h₁ : Q x = (x + 1/2)^2 + 8003/4): Q x >= 8003/4   :=  by sorry
