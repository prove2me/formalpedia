-- Prove2me | Theorems.Thm_PowerSumSharpness_multiset_zero_two_ne_one_one
-- name    : PowerSumSharpness.multiset_zero_two_ne_one_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:51:32.309422+00:00
-- url     : https://prove2.me/theorems/861b1400-5b24-483b-becd-dc97fbf92ab9
-- title:
--   The classical minimal witness: the two-point data sets `{0, 2}` and `{1, 1}` are bounded
-- statement:
--   The classical minimal witness: the two-point data sets `{0, 2}` and `{1, 1}` are bounded
--   by `2`, have the same power sums for `k ≤ 1`, and are different — the `N = 2` instance of
--   `powerSums_not_determined_of_lt`.
--
--   ```lean
--   theorem PowerSumSharpness.multiset_zero_two_ne_one_one:
--       (∀ x ∈ ({0, 2} : Multiset ℕ), x ≤ 2) ∧ (∀ x ∈ ({1, 1} : Multiset ℕ), x ≤ 2) ∧
--       (∀ k ≤ 1, (({0, 2} : Multiset ℕ).map (fun x => x ^ k)).sum
--         = (({1, 1} : Multiset ℕ).map (fun x => x ^ k)).sum) ∧
--       (({0, 2} : Multiset ℕ).map (fun x => x ^ 2)).sum
--         ≠ (({1, 1} : Multiset ℕ).map (fun x => x ^ 2)).sum ∧
--       ({0, 2} : Multiset ℕ) ≠ ({1, 1} : Multiset ℕ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PowerSumSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PowerSumSharpness.lean#L458

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

theorem PowerSumSharpness.multiset_zero_two_ne_one_one:
    (∀ x ∈ ({0, 2} : Multiset ℕ), x ≤ 2) ∧ (∀ x ∈ ({1, 1} : Multiset ℕ), x ≤ 2) ∧
    (∀ k ≤ 1, (({0, 2} : Multiset ℕ).map (fun x => x ^ k)).sum
      = (({1, 1} : Multiset ℕ).map (fun x => x ^ k)).sum) ∧
    (({0, 2} : Multiset ℕ).map (fun x => x ^ 2)).sum
      ≠ (({1, 1} : Multiset ℕ).map (fun x => x ^ 2)).sum ∧
    ({0, 2} : Multiset ℕ) ≠ ({1, 1} : Multiset ℕ) := by sorry
