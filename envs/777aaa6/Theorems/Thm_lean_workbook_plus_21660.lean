-- Prove2me | Theorems.Thm_lean_workbook_plus_21660
-- name    : lean_workbook_plus_21660
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/53751ca2-5a9e-4277-8e35-7ad1d3182504
-- statement:
--   $\left(n-\left(\frac{n}{2}-2\right)\right)\left(\left(\frac{n}{2}-2\right)+2\right)<100\implies n(n+4)<400 \implies n\le18$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21660 (n : ℕ) : (n - (n / 2 - 2)) * ((n / 2 - 2) + 2) < 100 → n * (n + 4) < 400 → n ≤ 18   :=  by sorry
