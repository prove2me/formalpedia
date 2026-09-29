-- Prove2me | Theorems.Thm_mme_finite_second_moment_many_above_threshold
-- name    : mme_finite_second_moment_many_above_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:41:56.08463+00:00
-- url     : https://prove2.me/theorems/118cd453-a702-4246-a8af-3c1f42d4b88e
-- title:
--   Finite second-moment bound for the number of above-threshold parameters
-- statement:
--   Let $f$ be a nonnegative real-valued function on a finite parameter set $U$, and let $h\ge0$ be at most half the mean of $f$. Then
--
--   $$
--   \left(\sum_{\omega\in U} f(\omega)\right)^2\le 4\,\bigl|\{\omega\in U:h\le f(\omega)\}\bigr|\sum_{\omega\in U}f(\omega)^2.
--   $$
--
--   This cross-multiplied finite Paley--Zygmund inequality converts first- and second-moment estimates into a lower bound on the number of parameters whose fiber degree exceeds a chosen threshold. It remains valid without dividing by $|U|$ or by the second moment, including degenerate finite sets.
-- source:
--   R. E. A. C. Paley and A. Zygmund, A note on analytic functions in the unit circle, Mathematical Proceedings of the Cambridge Philosophical Society 28 (1932), 266--272; finite counting-measure form of the Paley--Zygmund second-moment inequality

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open BigOperators

theorem mme_finite_second_moment_many_above_threshold
    {Ω : Type} [DecidableEq Ω]
    (U : Finset Ω) (f : Ω → ℝ) (h : ℝ)
    (hf : ∀ ω ∈ U, 0 ≤ f ω)
    (hh : 0 ≤ h)
    (hhalf : 2 * (U.card : ℝ) * h ≤ ∑ ω ∈ U, f ω) :
    (∑ ω ∈ U, f ω) ^ 2 ≤
      4 * ((U.filter (fun ω => h ≤ f ω)).card : ℝ) *
        (∑ ω ∈ U, (f ω) ^ 2) := by
  sorry
