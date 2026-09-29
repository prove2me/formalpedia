-- Prove2me | Theorems.Thm_QubitTrade_recordGcd_dvd_mem
-- name    : QubitTrade.recordGcd_dvd_mem
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:50:35.362548+00:00
-- url     : https://prove2.me/theorems/8a191ad7-6e63-4b64-974b-604f09acbe01
-- title:
--   The joint gcd of a record divides each of its entries.
-- statement:
--   The joint gcd of a record divides each of its entries.
--
--   ```lean
--   theorem QubitTrade.recordGcd_dvd_mem{k : ℕ} {ks : List ℕ} (hk : k ∈ ks) : recordGcd ks ∣ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/SampleFungibility.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/SampleFungibility.lean#L106

-- Thm stub generated from Algebra/QubitTrade/SampleFungibility.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SampleFungibility

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

open QubitTrade





/-! ## Records of arbitrary length -/

theorem QubitTrade.recordGcd_dvd_mem{k : ℕ} {ks : List ℕ} (hk : k ∈ ks) : recordGcd ks ∣ k := by sorry
