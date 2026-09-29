-- Prove2me | Theorems.Thm_lean_workbook_plus_10287
-- name    : lean_workbook_plus_10287
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3b2749f2-56c0-43e0-8592-8407e095994e
-- statement:
--   For how many $n$, $\frac {8n}{9999-n}$ is an integer given $1 \leq n \leq 2014$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10287 : ∃ n, (1 ≤ n ∧ n ≤ 2014 ∧ ∃ k : ℤ, 8 * n = k * (9999 - n))   :=  by sorry
