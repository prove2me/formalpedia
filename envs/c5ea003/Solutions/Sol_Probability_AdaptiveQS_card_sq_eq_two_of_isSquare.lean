-- Prove2me | solution 1 for Probability.AdaptiveQS.card_sq_eq_two_of_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:00.120824+00:00
-- url     : https://prove2.me/submissions/285b2732-bd20-4a8b-a948-b92f30fc5d8a

-- Sol generated from Probability/AdaptiveQSResidueRate.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSResidueRate
import Definitions.Def_Probability_AdaptiveQSSkipFlip
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



/-! ## The rate dial -/








/-! ## End-to-end deployment on a factor base -/





open Probability.AdaptiveQS in
theorem solution{p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {N : ZMod p}
    (hN : N ≠ 0) (h : IsSquare N) :
    (Finset.univ.filter (fun x : ZMod p => x ^ 2 = N)).card = 2 := by
  obtain ⟨b, hb⟩ := h
  have hb0 : b ≠ 0 := by
    intro h0
    exact hN (by rw [hb, h0, mul_zero])
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have hcast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at hcast
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hcast)
  have hne : b ≠ -b := by
    intro hbb
    apply hb0
    have h2b : (2 : ZMod p) * b = 0 := by linear_combination hbb
    rcases mul_eq_zero.mp h2b with h' | h'
    · exact absurd h' h2
    · exact h'
  have hset : (Finset.univ.filter (fun x : ZMod p => x ^ 2 = N)) = {b, -b} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      have hfac : (x - b) * (x + b) = 0 := by rw [hb] at hx; linear_combination hx
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact Or.inl (sub_eq_zero.mp h')
      · exact Or.inr (eq_neg_of_add_eq_zero_left h')
    · rintro (rfl | rfl) <;> rw [hb] <;> ring
  rw [hset, Finset.card_pair hne]
