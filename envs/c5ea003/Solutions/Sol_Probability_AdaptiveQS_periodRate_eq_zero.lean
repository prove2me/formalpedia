-- Prove2me | solution 1 for Probability.AdaptiveQS.periodRate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:23:33.959273+00:00
-- url     : https://prove2.me/submissions/a254f0b4-d3bf-46d8-ba3a-ee88f0b53c5e

-- Sol generated from Probability/AdaptiveQSResidueRate.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSResidueRate
import Definitions.Def_Probability_AdaptiveQSSkipFlip
import Theorems.Thm_Probability_AdaptiveQS_card_window_eq_card_zmod
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The exact per-period rate of a factor-base prime, and the QR dial it induces

Third cycle on experiment 559.  `Probability.AdaptiveQSSkipFlip` shows that a prime for
which `N` is a quadratic **non**-residue divides no sieve value at all
(`nonresidue_not_dvd_qsValue`).  That is only the null half of the mechanism.  This file
proves the *live* half exactly, and thereby computes the dial the experiment used.

For an odd prime `p` with `N ≢ 0`, the congruence `x² ≡ N (mod p)` has

* exactly `2` solutions per period when `N` is a quadratic residue
  (`card_sq_eq_two_of_isSquare`), and
* exactly `0` otherwise (`card_sq_eq_zero_of_not_isSquare`).

So the per-period hit rate of a factor-base prime is exactly `2/p` or `0`
(`periodRate_eq_two_div`, `periodRate_eq_zero`) — the `QR(≤100)` dial is not a heuristic
proxy for the rate, it *is* the rate, up to the deterministic factor `2/p`.  Three
consequences are then formalised.

* `periodRate_antitone_on_admissible` — among admissible primes the rate is decreasing in
  `p`: small admissible primes carry the yield.  This is the structural reason the
  rate-concentrator gains and inverse-rate spreading loses.
* `factorBase_skip_throughput_ge` — the end-to-end deployment statement: skipping a
  factor base by the rate dial never lowers the throughput, and
  `factorBase_skip_throughput_gt` gives the strict gain as soon as one genuinely worse
  prime is deferred.
* `nullPrime_transfer_gain` — moving budget off an inadmissible prime onto an admissible
  one strictly increases the yield, which is the "defer, don't sieve deeper" instrument in
  its exact arithmetic form.
-/

open Probability.AdaptiveQS

open Finset

/-! ## Exact solution counts -/


/-- **No solutions.**  If `N` is a quadratic non-residue mod `p` the congruence has no
solution: the exact null half of the mechanism. -/
theorem card_sq_eq_zero_of_not_isSquare {p : ℕ} [Fact p.Prime] {N : ZMod p}
    (h : ¬ IsSquare N) :
    (Finset.univ.filter (fun x : ZMod p => x ^ 2 = N)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  exact h ⟨x, by rw [← hx]; ring⟩

/-! ## The rate dial -/








/-! ## End-to-end deployment on a factor base -/





open Probability.AdaptiveQS in
theorem solution{p : ℕ} [Fact p.Prime] {N : ℤ}
    (h : ¬ IsSquare ((N : ZMod p))) : periodRate N p = 0 := by
  rw [periodRate, card_window_eq_card_zmod p N, card_sq_eq_zero_of_not_isSquare h]
  simp
