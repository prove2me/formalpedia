-- Prove2me | Theorems.Thm_mme_finite_variance_lower_tail_gap_card
-- name    : mme_finite_variance_lower_tail_gap_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T00:31:36.335011+00:00
-- url     : https://prove2.me/theorems/e36cb3f1-60ac-4b04-8b50-871b71c105c5
-- title:
--   A finite variance budget controls any fixed lower-tail gap
-- statement:
--   Let f be real-valued on a finite set U, and suppose its squared deviation from a reference μ has total at most V. For every gap δ≥0, the lower-tail set B={ω∈U:f(ω)+δ≤μ} satisfies $$δ^2|B|≤V.$$ This cross-multiplied one-sided Chebyshev inequality allows thresholds arbitrarily close to the mean and requires no division by δ.
-- source:
--   Finite one-sided Chebyshev inequality with an arbitrary lower-tail gap

import Mathlib

open BigOperators

set_option autoImplicit false

theorem mme_finite_variance_lower_tail_gap_card
    {Ω : Type} [DecidableEq Ω]
    (U : Finset Ω) (f : Ω → ℝ) (μ δ V : ℝ)
    (hδ : 0 ≤ δ)
    (hvar : ∑ ω ∈ U, (f ω - μ) ^ 2 ≤ V) :
    δ ^ 2 * ((U.filter (fun ω => f ω + δ ≤ μ)).card : ℝ) ≤ V := by
  sorry
