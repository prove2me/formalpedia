-- Prove2me | Theorems.Thm_lean_workbook_plus_72459
-- name    : lean_workbook_plus_72459
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/63a69028-3eac-40de-a2b6-f4defa68735e
-- statement:
--   If $2|n$ and $3|n$ , then $6|n$ . We can show that $(n)(n+1)(2n+1) \equiv 0 \mod 2, 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72459 (n : ℕ) (h1 : 2 ∣ n) (h2 : 3 ∣ n) : 6 ∣ n   :=  by sorry
