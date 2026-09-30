-- Prove2me | Theorems.Thm_Hirsch_finite_affine_envelope_crossing_sequence
-- name    : Hirsch.finite_affine_envelope_crossing_sequence
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T04:01:14.822116+00:00
-- url     : https://prove2.me/theorems/8b5a47c4-8e01-4823-9014-ed546f69991f
-- title:
--   Construct a stationary-free finite affine crossing itinerary with the additive factor-state bound
-- statement:
--   For finitely many nonempty finite dictionaries of real affine scores a_i(q)+t*b_i(q), assume each intercept list is injective and prescribe the unique winners at times 0 and 1. There exists an actual finite crossing itinerary with those endpoint tuples, strictly increasing sample times in (0,1), unique winners at every retained sample, no stationary adjacent tuple, and a wall strictly between each pair of samples where both neighboring tuples maximize every component score. The number of retained transitions is at most sum_i(k_i-1). The finite roots, their ordering, interval winners, closed-boundary comparisons, stationary compression and wall parameters are conclusions, not input certificates. This remains valid with simultaneous ties, unused crossings, parallel score lines, singleton factors and no factors. Scalar simultaneous ties alone do not imply a geometric edge: the separate accepted genericity theorem and compiled crossing geometry provide that additional step. No arbitrary-polytope diameter theorem or universally useful Minkowski decomposition is asserted.
-- source:
--   Classical finite affine-envelope construction. The slope-rank count proof is reused from accepted PR #239, research/publication_packets/simultaneous_envelope_edges/solution.lean, Git blob c6ea054c19c061539eba3f19427fd9ec6ef17336, with namespace/declaration renaming only. Finite root ordering uses Mathlib/Data/Finset/Sort.lean at the committed pin. New work constructs the complete chronological finite itinerary and compresses stationary states, closing the finite crossing-sequence obligation recorded after #242. No classical mathematical novelty claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.finite_affine_envelope_crossing_sequence
    (m : ℕ) (k : Fin m → ℕ)
    (a b : (i : Fin m) → Fin (k i) → ℝ)
    (p0 p1 : (i : Fin m) → Fin (k i))
    (ha : ∀ i, Function.Injective (a i))
    (hp0 : ∀ i q, q ≠ p0 i → a i q < a i (p0 i))
    (hp1 : ∀ i q, q ≠ p1 i → a i q + b i q < a i (p1 i) + b i (p1 i)) :
    ∃ (N : ℕ) (time : ℕ → ℝ)
      (pick : ℕ → (i : Fin m) → Fin (k i)),
      N ≤ ∑ i, (k i-1) ∧ pick 0 = p0 ∧ pick N = p1 ∧
      (∀ j, j < N → time j < time (j+1)) ∧
      (∀ j, j ≤ N → 0 < time j ∧ time j < 1 ∧
        ∀ i q, q ≠ pick j i →
          a i q+time j*b i q < a i (pick j i)+time j*b i (pick j i)) ∧
      (∀ j, j < N → pick j ≠ pick (j+1)) ∧
      (∀ j, j < N → ∃ u : ℝ, time j < u ∧ u < time (j+1) ∧
        (∀ i q, a i q+u*b i q ≤ a i (pick j i)+u*b i (pick j i)) ∧
        (∀ i, a i (pick (j+1) i)+u*b i (pick (j+1) i) =
          a i (pick j i)+u*b i (pick j i))) := by sorry
