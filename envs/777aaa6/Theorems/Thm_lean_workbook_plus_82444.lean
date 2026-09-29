-- Prove2me | Theorems.Thm_lean_workbook_plus_82444
-- name    : lean_workbook_plus_82444
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/45b2c430-a7ba-41b1-99de-91e66aa5d98e
-- statement:
--   Prove by induction: $1 + \frac{1}{{\sqrt 2 }} + \frac{1}{{\sqrt 3 }} + ... + \frac{1}{{\sqrt n }} < 2(\sqrt{n + 1} - 1)$ \n∀ n ∈ N
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82444 : ∀ n : ℕ, (∑ k in Finset.range n, (1 / Real.sqrt (k + 1))) < 2 * (Real.sqrt (n + 1) - 1)   :=  by sorry
