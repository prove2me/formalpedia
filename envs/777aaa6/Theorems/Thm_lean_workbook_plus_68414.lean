-- Prove2me | Theorems.Thm_lean_workbook_plus_68414
-- name    : lean_workbook_plus_68414
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/c16cddf2-e3f4-4595-9a19-09c20ec9506a
-- statement:
--   For all positive integers $n$ and $k,$ and $n>1,$ prove that $n^k-1$ is divisible by $n-1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68414 (n k : ℕ) (hn : 1 < n) : n - 1 ∣ n ^ k - 1   :=  by sorry
