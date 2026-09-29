-- Prove2me | solution 1 for QubitTrade.samples_recover_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:58:59.455423+00:00
-- url     : https://prove2.me/submissions/08a44dee-fb30-4168-b67b-e01e6f4ea1aa

-- Sol generated from Algebra/QubitTrade/SampleFungibility.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Theorems.Thm_QubitTrade_recordGcd_dvd_mem
import Theorems.Thm_QubitTrade_recovered_eq
import Theorems.Thm_QubitTrade_samples_recover

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






/-- If every sample's reduced denominator divides `d`, so does the record estimate. -/
theorem recordEstimate_dvd_of_forall {r d : ℕ} :
    ∀ {ks : List ℕ}, (∀ k ∈ ks, recovered k r ∣ d) → recordEstimate ks r ∣ d := by
  intro ks
  induction ks with
  | nil => intro _; simp [recordEstimate]
  | cons a l ih =>
      intro h
      exact Nat.lcm_dvd (h a (List.mem_cons_self ..))
        (ih fun k hk => h k (List.mem_cons_of_mem _ hk))




/-! ## Two samples suffice -/




open QubitTrade in
theorem solution{r : ℕ} {ks : List ℕ} (hr : 0 < r) :
    recordEstimate ks r = r ↔ Nat.gcd (recordGcd ks) r = 1 := by
  refine ⟨fun h => ?_, samples_recover hr⟩
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpr : p ∣ r := hpg.trans (Nat.gcd_dvd_right _ _)
  have hppos : 0 < p := hp.pos
  have hrp : 0 < r / p := Nat.div_pos (Nat.le_of_dvd hr hpr) hppos
  -- every sample's reduced denominator divides `r / p`
  have hstep : ∀ k ∈ ks, recovered k r ∣ r / p := by
    intro k hk
    have hpk : p ∣ k := hpg.trans ((Nat.gcd_dvd_left _ _).trans (recordGcd_dvd_mem hk))
    have hpgcd : p ∣ Nat.gcd k r := Nat.dvd_gcd hpk hpr
    obtain ⟨g', hg'⟩ := hpgcd
    have hgr : Nat.gcd k r ∣ r := Nat.gcd_dvd_right _ _
    have hrg : (r / Nat.gcd k r) * Nat.gcd k r = r := Nat.div_mul_cancel hgr
    refine ⟨g', ?_⟩
    rw [recovered_eq hr]
    refine Nat.div_eq_of_eq_mul_left hppos ?_
    calc r = (r / Nat.gcd k r) * Nat.gcd k r := hrg.symm
      _ = (r / Nat.gcd k r) * (p * g') := by rw [← hg']
      _ = (r / Nat.gcd k r) * g' * p := by ring
  have hL : recordEstimate ks r ∣ r / p := recordEstimate_dvd_of_forall hstep
  rw [h] at hL
  have : r ≤ r / p := Nat.le_of_dvd hrp hL
  have hlt : r / p < r := Nat.div_lt_self hr hp.one_lt
  omega
