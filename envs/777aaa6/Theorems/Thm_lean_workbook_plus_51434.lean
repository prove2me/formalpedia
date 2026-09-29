-- Prove2me | Theorems.Thm_lean_workbook_plus_51434
-- name    : lean_workbook_plus_51434
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e5e350fe-91d1-4991-a63f-c739b689bee8
-- statement:
--   Prove that $a^{log_bc}=c^{log_ba}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51434 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a^(Real.log c / Real.log b) = c^(Real.log a / Real.log b)   :=  by sorry
