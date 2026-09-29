-- Prove2me | Theorems.Thm_lean_workbook_plus_80258
-- name    : lean_workbook_plus_80258
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/ce81dd16-e1e5-4528-b7b8-145ab691691a
-- statement:
--   If $n$ is odd, then $n^5$ and $n$ are both odd, which means $n^5-n$ is even. The same applies when $n$ is even. Hence, $n^5-n$ is divisible by $2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80258  (n : ℤ)
  (h₀ : Odd n) :
  2 ∣ (n^5 - n)   :=  by sorry
