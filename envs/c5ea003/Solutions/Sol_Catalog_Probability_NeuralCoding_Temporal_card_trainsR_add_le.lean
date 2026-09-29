-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.card_trainsR_add_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:13:50.120903+00:00
-- url     : https://prove2.me/submissions/03260439-b7c4-4e8b-826e-5fe2ff83c222

-- Sol generated from Probability/RefractoryGeneralized.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_card_trainsR_small
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_trainsR_disjoint
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









theorem trainsR_succ (r n : ℕ) :
    trainsR r (n + 1) =
      (trainsR r n).image (fun l => false :: l) ∪
        (if r ≤ n then
            (trainsR r (n - r)).image (fun l => true :: (List.replicate r false ++ l))
          else {true :: List.replicate n false}) := by rw [trainsR]



/-- **Capacity recursion.**  The number of admissible trains in `n + 1` bins is the
number in `n` bins (silent first bin) plus the number in `n - r` bins (a spike
followed by `r` forced silent bins), the second term degenerating to `1` when the
window is shorter than the refractory period. -/
theorem card_trainsR_succ (r n : ℕ) :
    (trainsR r (n + 1)).card =
      (trainsR r n).card + (if r ≤ n then (trainsR r (n - r)).card else 1) := by
  rw [trainsR_succ, Finset.card_union_of_disjoint (trainsR_disjoint r n),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  by_cases hr : r ≤ n
  · rw [if_pos hr, if_pos hr,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  · rw [if_neg hr, if_neg hr, Finset.card_singleton]





/-- Capacity is monotone in the window length. -/
theorem card_trainsR_mono (r : ℕ) : ∀ n : ℕ, (trainsR r n).card ≤ (trainsR r (n + 1)).card := by
  intro n
  rw [card_trainsR_succ]
  omega

theorem card_trainsR_mono' (r : ℕ) {m n : ℕ} (h : m ≤ n) :
    (trainsR r m).card ≤ (trainsR r n).card := by
  induction n with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (card_trainsR_mono r n)
      · have : m = n + 1 := by omega
        subst this; exact le_rfl

/-- A one-bin extension of the window at most doubles the capacity. -/
theorem card_trainsR_succ_le (r n : ℕ) :
    (trainsR r (n + 1)).card ≤ 2 * (trainsR r n).card := by
  rw [card_trainsR_succ]
  by_cases hr : r ≤ n
  · rw [if_pos hr]
    have := card_trainsR_mono' r (show n - r ≤ n by omega)
    omega
  · rw [if_neg hr]
    have : 1 ≤ (trainsR r n).card := by
      have := card_trainsR_small r n (by omega)
      omega
    omega




















open Catalog.Probability.NeuralCoding.Temporal in
theorem solution(r : ℕ) : ∀ (k n : ℕ),
    (trainsR r (n + k)).card ≤ 2 ^ k * (trainsR r n).card := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro n
      calc (trainsR r (n + (k + 1))).card
          = (trainsR r ((n + k) + 1)).card := by ring_nf
        _ ≤ 2 * (trainsR r (n + k)).card := card_trainsR_succ_le r (n + k)
        _ ≤ 2 * (2 ^ k * (trainsR r n).card) := by
            exact Nat.mul_le_mul_left _ (ih n)
        _ = 2 ^ (k + 1) * (trainsR r n).card := by ring
