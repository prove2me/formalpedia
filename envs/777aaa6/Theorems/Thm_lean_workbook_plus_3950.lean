-- Prove2me | Theorems.Thm_lean_workbook_plus_3950
-- name    : lean_workbook_plus_3950
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6fde6c8f-b418-4057-a782-35bf5381540d
-- statement:
--   Another way is to observe that, for integers $n$ and $k$ , $(3n + k)^3 = 27n^3 + 27nk^2 + 9n^2k + k^3 \equiv k^3 \mod 9.$ Since any integer can be written as $3n + k$ for $k = 0$ , $1$ , or $2$ , it follows that its cube must be congruent to $0^3$ , $1^3$ , or $2^3$ mod $9$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3950  (n k : ℤ)
  (h₀ : 0 ≤ k ∧ k ≤ 2) :
  (3 * n + k)^3 % 9 = k^3 % 9   :=  by sorry
