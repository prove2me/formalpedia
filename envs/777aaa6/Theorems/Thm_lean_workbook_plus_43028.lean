-- Prove2me | Theorems.Thm_lean_workbook_plus_43028
-- name    : lean_workbook_plus_43028
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/541f09e1-419c-42cc-885e-8e7a43be9c24
-- statement:
--   Using $\lfloor x + 1/2 \rfloor = \lfloor 2x \rfloor - \lfloor x \rfloor$ , we get $S_n = \sum_{k=0}^n \left( \left\lfloor \frac{x}{2^k} \right\rfloor - \left\lfloor \frac{x}{2^{k+1}} \right\rfloor \right) = \lfloor x \rfloor - \left\lfloor \frac{x}{2^{n+1}} \right\rfloor.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43028 (x : ℝ) (n : ℕ) : ∑ k in Finset.range (n + 1), (Int.floor (x / 2^k) - Int.floor (x / 2^(k + 1))) = Int.floor x - Int.floor (x / 2^(n + 1))   :=  by sorry
