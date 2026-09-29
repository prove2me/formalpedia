-- Prove2me | Theorems.Thm_lean_workbook_plus_60210
-- name    : lean_workbook_plus_60210
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5f5909ec-6bff-4376-905c-6a410bfe5650
-- statement:
--   Lemma: $n^{\frac{n}{2}}\leq n!\leq n^n$ . The right inequality is obvious, since $n!$ is the product of $n$ integers $\leq n$ . The left side follows from $(n!)^2=\prod\limits_{k=1}^nk(n+1-k)\geq\prod\limits_{k=1}^nn$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60210 : ∀ n : ℕ, (n : ℝ)^(n / 2) ≤ n! ∧ n! ≤ n^n   :=  by sorry
