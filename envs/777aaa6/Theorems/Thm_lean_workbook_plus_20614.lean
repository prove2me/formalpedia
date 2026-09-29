-- Prove2me | Theorems.Thm_lean_workbook_plus_20614
-- name    : lean_workbook_plus_20614
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/93eae636-0a60-476b-8194-e195e38d8214
-- statement:
--   if $x$ is odd then $x^{2}$ can only be congurent to $1$ $mod$ $8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20614 {x : ℤ} (h : x%2 = 1) : x ^ 2 ≡ 1 [ZMOD 8]   :=  by sorry
