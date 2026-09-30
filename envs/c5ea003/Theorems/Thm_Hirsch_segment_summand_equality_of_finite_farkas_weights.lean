-- Prove2me | Theorems.Thm_Hirsch_segment_summand_equality_of_finite_farkas_weights
-- name    : Hirsch.segment_summand_equality_of_finite_farkas_weights
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T19:09:20.395009+00:00
-- url     : https://prove2.me/theorems/7ad7d8d9-d9e9-424b-b0bb-09c0c52c0f13
-- title:
--   Finite nonnegative Farkas weights certify an exact segment Minkowski summand
-- statement:
--   Let a finite halfspace system be given, together with a direction g and nonnegative length τ. For every original row that increases along g and every original row that decreases along g, suppose there is a nonnegative combination of the original inequalities whose normal is the corresponding opposing-row combination and whose constant certifies at least τ units of fiber width. Then the whole halfspace set is exactly the Minkowski sum of its endpoint erosion by the segment [0,τg] and that segment. The statement uses only the original rows and finite nonnegative weights; no proposed residual polytope or vertex enumeration is assumed.
-- source:
--   Corrected public-symbol-only packet extracted from PR #210 segment-peeling work after an earlier custom-preamble registration received WA: https://github.com/jjoshua2/prove2me-work/blob/formal/dual-wall-carrier-routing/research/publication_packets/pr210_catchup/segment_farkas_inline/solution.lean

import Mathlib
open Set
open scoped BigOperators

theorem Hirsch.segment_summand_equality_of_finite_farkas_weights
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ)
    (hτ : 0 ≤ τ) (hplus : ∃ i, 0 < a i g)
    (cert : ∀ i j, 0 < a i g → a j g < 0 →
      ∃ w : ι → ℝ,
        (∀ k, 0 ≤ w k) ∧
        (∑ k, w k • a k) = (-a j g) • a i + (a i g) • a j ∧
        (∑ k, w k * b k) ≤
          (-a j g) * b i + (a i g) * b j - τ * (a i g) * (-a j g)) :
    {x : E | ∀ i, a i x ≤ b i} =
      {x : E | ∃ p : E,
        (∀ i, a i p ≤ b i - τ * max (a i g) 0) ∧
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ τ ∧ x = p + t • g} := by sorry
