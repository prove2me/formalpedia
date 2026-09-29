-- Prove2me | Theorems.Thm_lean_workbook_plus_30405
-- name    : lean_workbook_plus_30405
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c86c9b6f-c815-4cad-9ad4-20ff6883d4c2
-- statement:
--   Prove that if $n^2$ is odd, then $n$ is odd.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30405 (n : ℤ) : n^2 % 2 = 1 → n % 2 = 1   :=  by sorry
