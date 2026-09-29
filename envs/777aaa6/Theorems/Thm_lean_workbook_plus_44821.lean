-- Prove2me | Theorems.Thm_lean_workbook_plus_44821
-- name    : lean_workbook_plus_44821
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/89427def-c863-48c6-ad18-9c178f80d5d1
-- statement:
--   Lemma: For $x > 0$, prove that $\frac{x}{x^3+9x+6}\leq \frac{3}{25x}+\frac{1}{100}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44821 (x : ℝ) (hx : 0 < x) : x / (x^3 + 9 * x + 6) ≤ 3 / (25 * x) + 1 / 100   :=  by sorry
