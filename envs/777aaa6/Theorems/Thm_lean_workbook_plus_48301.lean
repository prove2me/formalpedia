-- Prove2me | Theorems.Thm_lean_workbook_plus_48301
-- name    : lean_workbook_plus_48301
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ad6d1080-c0a8-4b57-85de-45447eb0f527
-- statement:
--   Prove $\sum_{k=0}^{k=n} \binom{p+k}{k}=\binom{p+n+1}{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48301 (p n : ℕ) : ∑ k in Finset.range (n+1), choose (p + k) k = choose (p + n + 1) n   :=  by sorry
