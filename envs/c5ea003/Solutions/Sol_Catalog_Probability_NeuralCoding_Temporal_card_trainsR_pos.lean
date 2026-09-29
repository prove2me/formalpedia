-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.card_trainsR_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:27:17.890093+00:00
-- url     : https://prove2.me/submissions/cf65b65b-769e-455b-953d-98c2534e5b94

-- Sol generated from Probability/RefractoryGeneralized.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_mem_trainsR_iff
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





/-- Prefixing silent bins does not affect admissibility. -/
theorem okB_replicate_false_append (r k : ℕ) (l : List Bool) :
    okB r (List.replicate k false ++ l) = okB r l := by
  induction k with
  | zero => simp
  | succ k ih => simpa [List.replicate_succ] using ih

@[simp] theorem okB_replicate_false (r k : ℕ) : okB r (List.replicate k false) = true := by
  have := okB_replicate_false_append r k []
  simpa using this

































open Catalog.Probability.NeuralCoding.Temporal in
theorem solution(r n : ℕ) : 0 < (trainsR r n).card := by
  refine Finset.card_pos.mpr ⟨List.replicate n false, ?_⟩
  exact (mem_trainsR_iff r n _).mpr ⟨by simp, by simp⟩
