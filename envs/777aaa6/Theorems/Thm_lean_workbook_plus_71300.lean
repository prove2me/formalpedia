-- Prove2me | Theorems.Thm_lean_workbook_plus_71300
-- name    : lean_workbook_plus_71300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ce2045dd-e324-49ce-96a1-72c4418a4fdc
-- statement:
--   Thus we want the number of $k$ such that $\frac{2013}{k}$ is reduced and satisfies $\frac{1}{1} < \frac{2013}{k} < 1000$ It is easy to see that this holds exactly for $3 \le k < 2013$ , and so we want the number of $k$ coprime to $2013$ in this range. $\phi(2013) = 1200$ , but we don't want to count $k = 1$ and $k = 2$ , so we get $1200 - 2 = 1198$ occurrences of the number $2013$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71300 :
  Finset.card (Finset.filter (λ k => Nat.gcd 2013 k = 1) (Finset.Icc 3 2012)) = 1198   :=  by sorry
