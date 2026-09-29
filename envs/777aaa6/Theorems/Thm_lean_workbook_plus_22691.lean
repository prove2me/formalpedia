-- Prove2me | Theorems.Thm_lean_workbook_plus_22691
-- name    : lean_workbook_plus_22691
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/475148ad-02b0-41a3-97f7-db761c69d2a9
-- statement:
--   if $d$ is a divisor of $n$ then $2^d-1$ is also a divisor of $2^n-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22691 {d n : ℕ} (h : d ∣ n) : 2 ^ d - 1 ∣ 2 ^ n - 1   :=  by sorry
