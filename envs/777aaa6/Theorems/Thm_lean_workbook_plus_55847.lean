-- Prove2me | Theorems.Thm_lean_workbook_plus_55847
-- name    : lean_workbook_plus_55847
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/5ceba3f8-20ea-4700-9cf8-a45384bf4668
-- statement:
--   Given that $\alpha$ and $\beta$ are the roots of equation $x^2 + px + q=0$ which implies $\alpha + \beta = -p$ and $\alpha \cdot \beta =q$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55847 : ∀ p q : ℂ, (p : ℂ) = - (α + β) ∧ (q : ℂ) = α * β   :=  by sorry
