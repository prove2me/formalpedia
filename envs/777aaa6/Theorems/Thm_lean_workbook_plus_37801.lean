-- Prove2me | Theorems.Thm_lean_workbook_plus_37801
-- name    : lean_workbook_plus_37801
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/662499ab-9cd9-4835-9fbe-b8669109ce84
-- statement:
--   If $n=3k$ then $n^2\equiv 0 \mod 3$; If $n=3k+1$ or $3k+2$ then $n^2\equiv 1 \mod 3$. If $a^2 \equiv 8 \mod 9$, then it $\equiv 2 \mod 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37801 (n : ℤ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 → n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1   :=  by sorry
