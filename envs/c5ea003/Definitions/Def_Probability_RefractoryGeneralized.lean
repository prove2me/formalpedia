-- Prove2me | Definitions.Def_Probability_RefractoryGeneralized
-- name    : Probability_RefractoryGeneralized
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:32.993044+00:00
-- url     : https://prove2.me/theorems/fbc1043b-8cf9-45b4-8cda-60d0c3ef47f1
-- title:
--   Aether Catalog definitions — Probability_RefractoryGeneralized
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.RefractoryGeneralized`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/RefractoryGeneralized.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Probability.NeuralCoding.Temporal

open Finset

/-- Admissibility of a spike train under an `r`-bin refractory period: after each
spike the next `r` bins (or all remaining bins, if fewer) must be silent. -/
def okB (r : ℕ) : List Bool → Bool
  | [] => true
  | (false :: l) => okB r l
  | (true :: l) => (l.take r).all (fun b => !b) && okB r l






/-- The admissible spike trains of a neuron with an `r`-bin refractory period in a
window of `n` bins.  A train either starts with a silent bin, or starts with a
spike, which must be followed by `r` silent bins (unless the window ends first). -/
def trainsR (r : ℕ) : ℕ → Finset (List Bool)
  | 0 => {[]}
  | (n + 1) =>
      (trainsR r n).image (fun l => false :: l) ∪
        (if r ≤ n then
            (trainsR r (n - r)).image (fun l => true :: (List.replicate r false ++ l))
          else {true :: List.replicate n false})































end Catalog.Probability.NeuralCoding.Temporal


