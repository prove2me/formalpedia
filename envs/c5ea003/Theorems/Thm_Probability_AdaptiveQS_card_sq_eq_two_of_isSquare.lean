-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_card_sq_eq_two_of_isSquare
-- name    : Probability.AdaptiveQS.card_sq_eq_two_of_isSquare
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:52:37.003348+00:00
-- url     : https://prove2.me/theorems/704b8e22-dd0a-4780-b0ba-fe52944ac484
-- title:
--   Two solutions per period.
-- statement:
--   **Two solutions per period.**  For an odd prime `p` and a nonzero quadratic residue
--   `N`, the congruence `x² ≡ N` has exactly two solutions mod `p`.
--
--   ```lean
--   theorem Probability.AdaptiveQS.card_sq_eq_two_of_isSquare{p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {N : ZMod p}
--       (hN : N ≠ 0) (h : IsSquare N) :
--       (Finset.univ.filter (fun x : ZMod p => x ^ 2 = N)).card = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSResidueRate.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSResidueRate.lean#L43

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

theorem Probability.AdaptiveQS.card_sq_eq_two_of_isSquare{p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {N : ZMod p}
    (hN : N ≠ 0) (h : IsSquare N) :
    (Finset.univ.filter (fun x : ZMod p => x ^ 2 = N)).card = 2 := by sorry
