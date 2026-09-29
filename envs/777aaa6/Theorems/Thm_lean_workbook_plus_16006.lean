-- Prove2me | Theorems.Thm_lean_workbook_plus_16006
-- name    : lean_workbook_plus_16006
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/abb53ffd-012a-45a4-9b3f-67b9fdbe045f
-- statement:
--   Prove that $\frac{bc}{b^2+c^2}=\frac{1}{\frac bc+\frac cb}=\frac{1}{2Re\; \frac bc}\in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16006 (b c : ℂ) :
  (b * c) / (b * b + c * c) = 1 / (b / c + c / b)   :=  by sorry
