-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.temporal_rate_two_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:35:03.780228+00:00
-- url     : https://prove2.me/submissions/51baeb29-b87d-456c-8edf-b618ff736ae7

-- Sol generated from Probability/RefractoryGeneralized.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_card_trainsR_pos
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_card_trainsR_two_step
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






















/-- **Two-bin refractory rate bound.**  In a window of `3m` bins a neuron with a
two-bin refractory period has at most `4 ^ m` spike trains: at most `2/3` of a bit
per time bin, strictly below the `4/5` available at `r = 1`. -/
theorem card_trainsR_two_le_pow : ∀ m : ℕ, (trainsR 2 (3 * m)).card ≤ 4 ^ m := by
  intro m
  induction m with
  | zero => simp [trainsR_zero]
  | succ m ih =>
      have e : 3 * (m + 1) = 3 * m + 3 := by ring
      rw [e]
      calc (trainsR 2 (3 * m + 3)).card ≤ 4 * (trainsR 2 (3 * m)).card :=
            card_trainsR_two_step (3 * m)
        _ ≤ 4 * 4 ^ m := Nat.mul_le_mul_left _ ih
        _ = 4 ^ (m + 1) := by ring









open Catalog.Probability.NeuralCoding.Temporal in
theorem solution(m : ℕ) :
    Real.logb 2 ((trainsR 2 (3 * m)).card) ≤ (2 / 3 : ℝ) * (3 * m) := by
  have h := card_trainsR_two_le_pow m
  have hcard : ((trainsR 2 (3 * m)).card : ℝ) ≤ (4 : ℝ) ^ m := by exact_mod_cast h
  have hpos : (0 : ℝ) < ((trainsR 2 (3 * m)).card : ℝ) := by
    exact_mod_cast card_trainsR_pos 2 (3 * m)
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hcard
  have h4 : Real.logb 2 ((4 : ℝ) ^ m) = 2 * m := by
    rw [Real.logb_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (b := (2 : ℝ)) (by norm_num)]
    ring
  rw [h4] at hlog
  calc Real.logb 2 ((trainsR 2 (3 * m)).card) ≤ 2 * (m : ℝ) := hlog
    _ = (2 / 3 : ℝ) * (3 * m) := by ring
