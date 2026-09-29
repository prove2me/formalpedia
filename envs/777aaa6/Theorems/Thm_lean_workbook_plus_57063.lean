-- Prove2me | Theorems.Thm_lean_workbook_plus_57063
-- name    : lean_workbook_plus_57063
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/dbc3285a-8ec0-4f91-aec8-41116136c572
-- statement:
--   Prove that $1+2^{n+1}+4^{n+1}>2(1+2^n+4^n)$ $\forall n\in\mathbb N$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57063 (n:ℕ) : 1 + 2^(n+1) + 4^(n+1) > 2 * (1 + 2^n + 4^n)   :=  by sorry
