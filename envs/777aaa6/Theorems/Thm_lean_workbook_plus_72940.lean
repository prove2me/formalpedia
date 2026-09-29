-- Prove2me | Theorems.Thm_lean_workbook_plus_72940
-- name    : lean_workbook_plus_72940
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b939c765-4253-408c-9570-9c3051e3125c
-- statement:
--   $D=-3 n^2+6 n+1\ge 0\Rightarrow n\in \{0,1,2\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72940 (D n: ℤ) (hn: D = -3 * n^2 + 6 * n + 1) (hD: D >= 0): n = 0 ∨ n = 1 ∨ n = 2   :=  by sorry
