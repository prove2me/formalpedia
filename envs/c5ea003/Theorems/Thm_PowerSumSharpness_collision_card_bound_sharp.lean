-- Prove2me | Theorems.Thm_PowerSumSharpness_collision_card_bound_sharp
-- name    : PowerSumSharpness.collision_card_bound_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:50:37.040705+00:00
-- url     : https://prove2.me/theorems/9c2f5309-36f0-4dfb-be78-f3fd02ebd744
-- title:
--   The collision-size bound is sharp for every `N`.
-- statement:
--   **The collision-size bound is sharp for every `N`.**  The even and odd halves of the
--   binomial data `C(N, ·)` are two different data sets bounded by `N`, of size exactly
--   `2^(N-1)`, whose power sums agree in every order `k < N`.  Together with
--   `multiset_collision_card_lower_bound` this pins down the exact threshold `2^(N-1)` at which
--   moment collisions of order `N - 1` begin to exist.
--
--   ```lean
--   theorem PowerSumSharpness.collision_card_bound_sharp{N : ℕ} (hN : 1 ≤ N) :
--       (∀ x ∈ evenMultiset N, x ≤ N) ∧ (∀ x ∈ oddMultiset N, x ≤ N) ∧
--       (∀ k < N, ((evenMultiset N).map (fun x => x ^ k)).sum
--         = ((oddMultiset N).map (fun x => x ^ k)).sum) ∧
--       evenMultiset N ≠ oddMultiset N ∧
--       Multiset.card (evenMultiset N) = 2 ^ (N - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PowerSumSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PowerSumSharpness.lean#L783

-- Thm stub generated from Probability/PowerSumSharpness.lean
import Mathlib
import Definitions.Def_Probability_PowerSumSharpness
/-
# Sharpness of the finite moment problem on `{0, 1, …, N}`

A "distribution" supported in `{0, 1, …, N}` is here a weight function `w : ℕ → ℝ`
(we only ever look at `w` on `Finset.range (N+1)`), and its *power sums* — the moments —
are `powerSum N w k = ∑ i ≤ N, w i * i ^ k`.

The file proves a complete rigidity/sharpness package.

* **Rigidity (`powerSum_determined`).**  Knowing the power sums for all `k ≤ N`
  determines the weights on `{0, …, N}`.  The proof is a Lagrange-interpolation
  (Vandermonde) argument packaged as `eq_zero_of_moments_zero`, which is stated for an
  arbitrary finite family of pairwise distinct real nodes.
* **Sharpness (`powerSums_not_determined_of_lt`).**  The range `k ≤ N` cannot be
  shortened: for every `K < N` there are two genuine probability distributions on
  `{0, …, N}` whose power sums agree for all `k ≤ K` yet which are different — the even
  and odd halves of the binomial weights `i ↦ C(N,i)/2^{N-1}`.  For `N = 2` this is
  exactly the classical pair `{0,2}` versus `{1,1}` (`multiset_zero_two_ne_one_one`).
* **Structure of the failure (`diff_eq_alternating`).**  The failure is *unique*: any two
  weight systems on `{0, …, N}` whose power sums agree for all `k < N` differ by a scalar
  multiple of the alternating binomial vector `i ↦ (-1)^i C(N,i)`.  Thus the collisions at
  `K = N - 1` form a one-parameter family and there are none at `K = N`.
* **Quantitative gap (`powerSum_gap_at_N`).**  For such a pair the `N`-th power sums differ
  by exactly `c · (-1)^N · N !`, where `c` is the weight discrepancy at the node `0`.
  This rests on the sharp alternating-sum identity `alternating_binom_eval`,
  `∑ i ≤ N, (-1)^i C(N,i) p(i) = (-1)^N N! · [X^N] p` for `deg p ≤ N`, proved by induction
  through a finite-difference (Pascal telescoping) argument.
* **Multiset form (`multiset_determined_by_powerSums`).**  Two multisets of naturals bounded
  by `N` with the same power sums `∑ x^k` for `k ≤ N` are equal.
-/

open Finset Polynomial

open PowerSumSharpness

/-! ## 1. A Vandermonde / Lagrange vanishing principle -/




/-! ## 2. Power sums of a weight system on `{0, …, N}` -/





/-! ## 3. The alternating binomial functional -/







/-! ## 4. Structure of the moment collisions at order `N - 1` -/





/-! ## 5. The sharpness construction: even and odd binomial halves -/













/-! ## 6. Multiset ("empirical distribution") formulation -/




/-! ## 7. How large must a moment collision be? -/




/-! ## 8. Machine-checked exhaustive search (small cases)

These two statements are the `N = 2` rows of the exhaustive search reported in
`ComputationalEvidence.md`, §8: among sorted tuples with entries in `{0,1,2}`, the pairs
with equal first power sums are exactly the ones predicted by `diff_eq_alternating`, i.e.
those whose count vectors differ by a multiple of `(1, -2, 1)`. -/



/-! ## 9. Extremal separation and stability -/





/-! ## 10. The collision-size bound `2^(N-1)` is attained for every `N` -/

theorem PowerSumSharpness.collision_card_bound_sharp{N : ℕ} (hN : 1 ≤ N) :
    (∀ x ∈ evenMultiset N, x ≤ N) ∧ (∀ x ∈ oddMultiset N, x ≤ N) ∧
    (∀ k < N, ((evenMultiset N).map (fun x => x ^ k)).sum
      = ((oddMultiset N).map (fun x => x ^ k)).sum) ∧
    evenMultiset N ≠ oddMultiset N ∧
    Multiset.card (evenMultiset N) = 2 ^ (N - 1) := by sorry
