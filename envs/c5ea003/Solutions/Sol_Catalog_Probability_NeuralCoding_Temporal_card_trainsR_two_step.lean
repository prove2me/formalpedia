-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.card_trainsR_two_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:27:18.427612+00:00
-- url     : https://prove2.me/submissions/a603c3c3-1caf-42d7-a5ee-45460d6d72f8

-- Sol generated from Probability/RefractoryGeneralized.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_card_trainsR_recursion
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_card_trainsR_small
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
















/-- **Refractory period `2`: Narayana's cows recursion** `c(n + 3) = c(n + 2) + c(n)`
(OEIS A000930), the `r = 2` instance of the general capacity recursion. -/
theorem card_trainsR_two_succ3 (n : ℕ) :
    (trainsR 2 (n + 3)).card = (trainsR 2 (n + 2)).card + (trainsR 2 n).card :=
  card_trainsR_recursion 2 n







theorem card_trainsR_two_zero : (trainsR 2 0).card = 1 := card_trainsR_small 2 0 (by omega)

theorem card_trainsR_two_one : (trainsR 2 1).card = 2 := card_trainsR_small 2 1 (by omega)

theorem card_trainsR_two_two : (trainsR 2 2).card = 3 := card_trainsR_small 2 2 (by omega)

theorem card_trainsR_two_three : (trainsR 2 3).card = 4 := by
  have := card_trainsR_two_succ3 0
  rw [card_trainsR_two_zero, card_trainsR_two_two] at this
  simpa using this

theorem card_trainsR_two_four : (trainsR 2 4).card = 6 := by
  have := card_trainsR_two_succ3 1
  rw [card_trainsR_two_one, card_trainsR_two_three] at this
  simpa using this

theorem card_trainsR_two_five : (trainsR 2 5).card = 9 := by
  have := card_trainsR_two_succ3 2
  rw [card_trainsR_two_two, card_trainsR_two_four] at this
  simpa using this











open Catalog.Probability.NeuralCoding.Temporal in
theorem solution: ∀ n : ℕ, (trainsR 2 (n + 3)).card ≤ 4 * (trainsR 2 n).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [card_trainsR_two_zero, card_trainsR_two_three]
    | 1 => rw [card_trainsR_two_one, card_trainsR_two_four]; omega
    | 2 => rw [card_trainsR_two_two, card_trainsR_two_five]; omega
    | (m + 3) =>
        have h1 : (trainsR 2 (m + 2 + 3)).card ≤ 4 * (trainsR 2 (m + 2)).card :=
          ih (m + 2) (by omega)
        have h2 : (trainsR 2 (m + 3)).card ≤ 4 * (trainsR 2 m).card := ih m (by omega)
        have hrec : (trainsR 2 (m + 3 + 3)).card
            = (trainsR 2 (m + 3 + 2)).card + (trainsR 2 (m + 3)).card :=
          card_trainsR_two_succ3 (m + 3)
        have hrec2 : (trainsR 2 (m + 3)).card
            = (trainsR 2 (m + 2)).card + (trainsR 2 m).card := card_trainsR_two_succ3 m
        have e : m + 2 + 3 = m + 3 + 2 := by ring
        rw [e] at h1
        omega
