-- Prove2me | Theorems.Thm_lean_workbook_plus_11559
-- name    : lean_workbook_plus_11559
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/491cc410-4866-4ee2-9b96-1ade6cac31f0
-- statement:
--   Prove that $ \sum_{k=1}^{n}(-1)^{k+1}k^{n-1}\sum_{r=k}^{n}\frac{k}{r}\binom{r}{k} = \sum_{k=1}^{n}(-1)^{k+1}k^{n-1}\sum_{r=k}^{n}\binom{r-1}{k-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11559 : ∀ n : ℕ, n > 0 → ∑ k in Finset.Icc 1 n, (-1 : ℤ)^(k+1) * k^(n-1) * (∑ r in Finset.Icc k n, k / r * (r.choose k)) = ∑ k in Finset.Icc 1 n, (-1 : ℤ)^(k+1) * k^(n-1) * (∑ r in Finset.Icc k n, (r-1).choose (k-1))   :=  by sorry
