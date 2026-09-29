-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_periodRate_eq_zero
-- name    : Probability.AdaptiveQS.periodRate_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:53:31.973983+00:00
-- url     : https://prove2.me/theorems/dd229fa8-6efc-43b8-aee0-66aaec6cf7e0
-- title:
--   An inadmissible prime has rate exactly `0`: the null equaliser at the level of rates.
-- statement:
--   An inadmissible prime has rate exactly `0`: the null equaliser at the level of rates.
--
--   ```lean
--   theorem Probability.AdaptiveQS.periodRate_eq_zero{p : ℕ} [Fact p.Prime] {N : ℤ}
--       (h : ¬ IsSquare ((N : ZMod p))) : periodRate N p = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSResidueRate.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSResidueRate.lean#L130

-- Thm stub generated from Probability/AdaptiveQSResidueRate.lean
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

theorem Probability.AdaptiveQS.periodRate_eq_zero{p : ℕ} [Fact p.Prime] {N : ℤ}
    (h : ¬ IsSquare ((N : ZMod p))) : periodRate N p = 0 := by sorry
