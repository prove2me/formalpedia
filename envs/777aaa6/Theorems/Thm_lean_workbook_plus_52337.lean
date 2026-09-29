-- Prove2me | Theorems.Thm_lean_workbook_plus_52337
-- name    : lean_workbook_plus_52337
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/c27a20e8-c422-4bfc-a147-c238fa633e85
-- statement:
--   Prove the Cauchy-Schwarz inequality: $(m^2+n^2)(p^2+q^2)\geq(mp+nq)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52337 (m n p q : ℝ) : (m^2 + n^2)*(p^2 + q^2) ≥ (m * p + n * q)^2   :=  by sorry
