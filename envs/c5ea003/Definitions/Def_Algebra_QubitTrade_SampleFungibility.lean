-- Prove2me | Definitions.Def_Algebra_QubitTrade_SampleFungibility
-- name    : Algebra_QubitTrade_SampleFungibility
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:58:17.371361+00:00
-- url     : https://prove2.me/theorems/48281233-f253-4f5a-9dd0-95be7ab48e7d
-- title:
--   Aether Catalog definitions — Algebra_QubitTrade_SampleFungibility
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.QubitTrade.SampleFungibility`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/QubitTrade/SampleFungibility.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution

/-!
# QUBIT-TRADE III: qubit ↔ sample fungibility above the threshold

Above the resolution threshold of `Resolution.lean` a truncated register still
does not hand you the order: continued fractions return the *reduced* fraction
`k/r`, whose denominator is `r / gcd (k, r)`, and a sample with `gcd (k, r) > 1`
under-reports the order.  This is the only remaining obstruction, and it is the
one that **more samples do repair** — the observed "qubit ↔ sample fungibility".

We prove this exactly:

* `QubitTrade.recovered_eq` — one sample returns `r / gcd (k, r)`, a proper
  divisor of `r` whenever `gcd (k, r) > 1` (`QubitTrade.recovered_lt`);
* `QubitTrade.two_samples_recover` — **two** samples whose numerators are jointly
  coprime to `r` already give `r` as the lcm of the two reduced denominators;
* `QubitTrade.samples_recover` — the same for a record of arbitrary length: the
  lcm of the reduced denominators equals `r` exactly when the numerators are
  jointly coprime to `r` (`QubitTrade.samples_recover_iff` gives the converse,
  so the criterion is sharp).

Combined with `Resolution.cf_target_unique` this is the positive half of the
trade: above `2 log₂ r` qubits, extra samples buy the missing gcd information —
but below it (see `SupportCollapse.lean`) no number of samples buys anything.
-/

namespace QubitTrade

/-- The order actually recovered from a single sample `k` at true order `r`:
the denominator of the reduced fraction `k / r`. -/
def recovered (k r : ℕ) : ℕ := (orderFrac k r).den




/-! ## Records of arbitrary length -/

/-- The joint gcd of a record of numerators. -/
def recordGcd (ks : List ℕ) : ℕ := ks.foldr Nat.gcd 0

/-- The order estimate produced from a record: the lcm of the reduced
denominators of all the samples. -/
def recordEstimate (ks : List ℕ) (r : ℕ) : ℕ :=
  (ks.map (fun k => recovered k r)).foldr Nat.lcm 1








/-! ## Two samples suffice -/



end QubitTrade


