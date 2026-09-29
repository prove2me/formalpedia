-- Prove2me | Theorems.Thm_lean_workbook_plus_51043
-- name    : lean_workbook_plus_51043
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5730f79b-5c12-48b7-8c30-ba1b2cf457de
-- statement:
--   ${ P(k+1)={7}^{k+1} -1}={(7)}({7}^k)-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51043 (k : ℕ) : 7^(1 + k) - 1 = 7 * 7^k - 1   :=  by sorry
