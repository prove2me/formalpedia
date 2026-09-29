-- Prove2me | Theorems.Thm_lean_workbook_plus_46033
-- name    : lean_workbook_plus_46033
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d415060b-51a1-441d-b19c-c93653943dd2
-- statement:
--   Induction: \n\n $n = 5 \implies 32 > 25$ which is obviously true. \n\n Assume it holds for $n = k$ \n\n $2^k > k^2$ \n\n Now since $k > 4, (k-1)^2 > 2 \implies k^2 > 2k+1 \implies 2k^2 > (k+1)^2$ \n\n From our inductive hypothesis, $2^k > k^2 \implies 2^{k+1} > 2k^2 > (k+1)^2$ from our result above. \n\n Therefore, $2^n > n^2$ for all $n > 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46033  (n : ℕ)
  (h₀ : 5 ≤ n) :
  (2^n) > n^2   :=  by sorry
