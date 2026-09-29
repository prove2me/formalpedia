-- Prove2me | Theorems.Thm_lean_workbook_plus_33863
-- name    : lean_workbook_plus_33863
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/10966233-ffe3-45d1-862c-d2fe4be6c504
-- statement:
--   The other factor yields $ n^2+5n+7=1\ implies (n+2)(n+3)=0 \implies n=-2, n=-3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33863 {n : ℤ} (hn : n^2 + 5*n + 7 = 1) : n = -2 ∨ n = -3   :=  by sorry
