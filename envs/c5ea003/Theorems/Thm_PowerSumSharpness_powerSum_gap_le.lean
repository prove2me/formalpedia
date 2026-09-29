-- Prove2me | Theorems.Thm_PowerSumSharpness_powerSum_gap_le
-- name    : PowerSumSharpness.powerSum_gap_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:52:51.617634+00:00
-- url     : https://prove2.me/theorems/5d6d4c5d-af40-436c-bf66-b8e530dceba0
-- title:
--   The extremal separation constant.
-- statement:
--   **The extremal separation constant.**  Among *probability* distributions on `{0, …, N}`
--   whose power sums agree in all orders `< N`, the `N`-th power sums can differ by at most
--   `N !/2^(N-1)`.  Equality holds for the even/odd binomial halves (`halves_gap_eq_extremal`),
--   so the constant is sharp.
--
--   ```lean
--   theorem PowerSumSharpness.powerSum_gap_le{N : ℕ} (hN : 1 ≤ N) {w v : ℕ → ℝ}
--       (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
--       (hw1 : powerSum N w 0 = 1) (hv1 : powerSum N v 0 = 1)
--       (h : ∀ k < N, powerSum N w k = powerSum N v k) :
--       |powerSum N w N - powerSum N v N| ≤ (N.factorial : ℝ) / 2 ^ (N - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PowerSumSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PowerSumSharpness.lean#L597

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

theorem PowerSumSharpness.powerSum_gap_le{N : ℕ} (hN : 1 ≤ N) {w v : ℕ → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hw1 : powerSum N w 0 = 1) (hv1 : powerSum N v 0 = 1)
    (h : ∀ k < N, powerSum N w k = powerSum N v k) :
    |powerSum N w N - powerSum N v N| ≤ (N.factorial : ℝ) / 2 ^ (N - 1) := by sorry
