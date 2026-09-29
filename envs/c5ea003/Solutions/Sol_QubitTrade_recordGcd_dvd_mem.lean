-- Prove2me | solution 1 for QubitTrade.recordGcd_dvd_mem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:01:58.310614+00:00
-- url     : https://prove2.me/submissions/f718975b-61f0-486e-8e6c-9932a5e4ca84

-- Sol generated from Algebra/QubitTrade/SampleFungibility.lean
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










/-! ## Two samples suffice -/




open QubitTrade in
theorem solution{k : ℕ} {ks : List ℕ} (hk : k ∈ ks) : recordGcd ks ∣ k := by
  induction ks with
  | nil => cases hk
  | cons a l ih =>
      rcases List.mem_cons.mp hk with rfl | hmem
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right a (recordGcd l)).trans (ih hmem)
