-- Prove2me | Theorems.Thm_lean_workbook_plus_46320
-- name    : lean_workbook_plus_46320
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/0a4085ac-f799-4fa3-8e9b-cfcdfba337ff
-- statement:
--   When $n$ is odd: $4^n + n^4= (2^n + n^2)^2 - n^22^{n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46320 (n : ℕ) (h : n % 2 = 1) : (4:ℤ)^n + n^4 = (2^n + n^2)^2 - n^2 * 2^(n+1)   :=  by sorry
