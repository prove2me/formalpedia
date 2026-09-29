-- Prove2me | Theorems.Thm_lean_workbook_plus_59015
-- name    : lean_workbook_plus_59015
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e410ca0b-72ff-49f4-8b99-f0cc0a77b4a0
-- statement:
--   Let $ p$ be a prime number and $ n$ is nonegative integer. The numbers $ x_1 , x_2 , x_3 , ...,x_s$ , are all numbers of the set : $ \{1,2,...,p^n\}$ ,who are relatively prime with $ p^n$ .Prove the equality : \n\n$x_1^3 + x_2^3 + ... + x_s^3 = \frac {1}{4}\cdot p^{2n}\cdot (p - 1)(p^{2n - 1} - 1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59015 (p n : ℕ) (hp : p.Prime)(h pn: 0 < n) :  ∑ k in (Finset.filter (λ x => Nat.Coprime x (p^n)) (Finset.Icc 1 (p^n))), k^3 = (1/4)*p^(2*n)*(p-1)*(p^(2*n-1)-1)   :=  by sorry
