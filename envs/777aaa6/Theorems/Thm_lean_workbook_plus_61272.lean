-- Prove2me | Theorems.Thm_lean_workbook_plus_61272
-- name    : lean_workbook_plus_61272
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/92302e2c-0956-40d9-a401-29ee4c4bbfa9
-- statement:
--   What is the sum of: $1^{3}+ 2^{3}+ 3^{3} + ....+ 20^{3}?$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61272 : ∑ k in Finset.range 21, k^3 = 44100   :=  by sorry
