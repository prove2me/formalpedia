-- Prove2me | Theorems.Thm_lean_workbook_plus_45843
-- name    : lean_workbook_plus_45843
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/575bc0e1-67d5-453b-a46a-f29db5f72e76
-- statement:
--   Use that $ (1-\frac{1}{4})(1-\frac{1}{9})(1-\frac{1}{16})\cdot...\cdot(1-\frac{1}{n^{2}}) =\frac{1}{2}\frac{(n-1)!(n+1)!}{(n!)^2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45843 : ∀ n : ℕ, (∏ k in Finset.Icc 2 n, (1 - 1 / k ^ 2)) = (1 / 2) * ((n - 1)! * (n + 1)! / (n!) ^ 2)   :=  by sorry
