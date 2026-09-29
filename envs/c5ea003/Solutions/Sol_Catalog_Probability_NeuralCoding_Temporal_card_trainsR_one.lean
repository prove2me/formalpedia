-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.card_trainsR_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:21:01.935853+00:00
-- url     : https://prove2.me/submissions/150981db-ba9b-4d94-9ac4-078717330bc9

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








theorem trainsR_zero (r : ℕ) : trainsR r 0 = {[]} := by rw [trainsR]































open Catalog.Probability.NeuralCoding.Temporal in
theorem solution: ∀ n : ℕ, (trainsR 1 n).card = Nat.fib (n + 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [trainsR_zero]
    | 1 => rw [card_trainsR_small 1 1 (le_refl 1)]; rfl
    | (m + 2) =>
        have h := card_trainsR_recursion 1 m
        rw [show m + 1 + 1 = m + 2 from by omega] at h
        have h1 : (trainsR 1 (m + 1)).card = Nat.fib (m + 3) := by
          have := ih (m + 1) (by omega)
          rwa [show m + 1 + 2 = m + 3 from by omega] at this
        have h2 : (trainsR 1 m).card = Nat.fib (m + 2) := ih m (by omega)
        have hf : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
        rw [show m + 2 + 2 = m + 4 from by omega, h, h1, h2]
        omega
