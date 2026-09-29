-- Prove2me | Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_temporal_rate_two_le
-- name    : Catalog.Probability.NeuralCoding.Temporal.temporal_rate_two_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:01:56.168945+00:00
-- url     : https://prove2.me/theorems/ae7eba70-2644-48e0-9af7-d3ce8d1cfba5
-- title:
--   Two-bin refractory rate.
-- statement:
--   **Two-bin refractory rate.**  A neuron with a two-bin refractory period transmits
--   at most `2/3` of a bit per time bin over a window of `3m` bins.
--
--   ```lean
--   theorem Catalog.Probability.NeuralCoding.Temporal.temporal_rate_two_le(m : ℕ) :
--       Real.logb 2 ((trainsR 2 (3 * m)).card) ≤ (2 / 3 : ℝ) * (3 * m) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/RefractoryGeneralized.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/RefractoryGeneralized.lean#L447

-- Thm stub generated from Probability/RefractoryGeneralized.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Temporal codes with an `r`-bin refractory period

`RefractorySpikeTrains.lean` (in this directory) treats the case of an absolute refractory period of
one time bin: no two spikes in *adjacent* bins, giving the Fibonacci capacity
`fib (T + 2)`.  Real neurons have a refractory period spanning several bins.
This file develops the general case: a spike must be followed by at least `r`
silent bins (a spike in one of the last `r` bins of the window is allowed, the
window simply ends).

## Results

1. `okB` — the admissibility predicate for an `r`-bin refractory period, and
   `trainsR`, an explicit finset of admissible spike trains defined by the
   refractory recursion.
2. `mem_trainsR_iff` — the recursion is correct: `trainsR r n` is *exactly* the
   set of length-`n` binary words in which every spike is followed by `r`
   silent bins (or by the end of the window).
3. `card_trainsR_succ`, `card_trainsR_recursion` — the capacity recursion
   `c_r(n + r + 1) = c_r(n + r) + c_r(n)`, whose characteristic equation is
   `x ^ (r + 1) = x ^ r + 1`.
4. `card_trainsR_one` — for `r = 1` the capacity is `fib (n + 2)`, recovering
   the theorem of `RefractorySpikeTrains.lean` from the general recursion.
5. `card_trainsR_two_succ3` — for `r = 2` the capacity obeys
   `c(n + 3) = c(n + 2) + c(n)` (Narayana's cows, OEIS A000930).
6. `trainsR_antitone`, `card_trainsR_antitone` — a longer refractory period can
   only lose capacity.
7. `card_trainsR_le_pow`, `temporal_rate_le_general` — a general rate bound:
   over a window of `(r + 1) * m` bins the capacity is at most `(2 ^ r + 1) ^ m`.
8. `card_trainsR_two_le_pow`, `temporal_rate_two_le` — the sharper `r = 2` bound
   `c(3m) ≤ 4 ^ m`, i.e. at most `2/3` of a bit per time bin (against `4/5` for
   `r = 1` and `1` for the unconstrained channel): refractoriness strictly
   decreases the information rate.
9. `card_trainsR_ge` — a matching lower bound `n + 1 ≤ c_r(n)`, so the capacity
   is never trivial.
-/

open Catalog.Probability.NeuralCoding.Temporal

open Finset

theorem Catalog.Probability.NeuralCoding.Temporal.temporal_rate_two_le(m : ℕ) :
    Real.logb 2 ((trainsR 2 (3 * m)).card) ≤ (2 / 3 : ℝ) * (3 * m) := by sorry
