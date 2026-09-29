-- Prove2me | Theorems.Thm_lean_workbook_plus_66907
-- name    : lean_workbook_plus_66907
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ec40e18f-85e2-4a59-8df2-0190c5ba7f15
-- statement:
--   Factor into $n(n+1)(2n+1)$ . Either $n$ or $n+1$ must be even, so for it to be divisible by 6, one of the terms must be divisible by 3. The only way $n$ or $n+1$ isn't divisible by 3 is if $n\equiv 1 \pmod 3$ and $n+1 \equiv 2 \pmod 3$ . However, in this case, $2n+1 \equiv 3 \equiv 0 \pmod 3$ , so one of the three terms is always divisible by 3, and thus the expression is always divisible by 6.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66907 : ∀ n : ℕ, 6 ∣ n * (n + 1) * (2 * n + 1)   :=  by sorry
