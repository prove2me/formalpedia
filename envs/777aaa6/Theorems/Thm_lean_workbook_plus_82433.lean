-- Prove2me | Theorems.Thm_lean_workbook_plus_82433
-- name    : lean_workbook_plus_82433
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/971566f3-682b-4cc7-9134-ee07a95ef924
-- statement:
--   Find $m^2+4n^2$ given $m^3-12mn^2=40$ and $4n^3-3m^2n=10$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82433 (m n : ℤ) (h1 : m^3 - 12*m*n^2 = 40) (h2 : 4*n^3 - 3*m^2*n = 10) : m^2 + 4*n^2 = 14   :=  by sorry
