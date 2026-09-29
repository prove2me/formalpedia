-- Prove2me | Theorems.Thm_lean_workbook_plus_16398
-- name    : lean_workbook_plus_16398
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0b71d4c9-9c70-4ddb-bee3-492031c804ab
-- statement:
--   Prove that $c^2+(1-c)^2<1$ when $0<c<1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16398 : ∀ c : ℝ, 0 < c ∧ c < 1 → c^2 + (1 - c)^2 < 1   :=  by sorry
