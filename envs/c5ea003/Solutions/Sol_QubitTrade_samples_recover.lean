-- Prove2me | solution 1 for QubitTrade.samples_recover
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:52:23.957125+00:00
-- url     : https://prove2.me/submissions/d400491f-f1e7-4c75-b9b4-aeac112ede80

-- Sol generated from Algebra/QubitTrade/SampleFungibility.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Theorems.Thm_QubitTrade_recovered_eq

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



theorem recovered_dvd {k r : ℕ} (hr : 0 < r) : recovered k r ∣ r := by
  rw [recovered_eq hr]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)


/-! ## Records of arbitrary length -/



theorem recordGcd_dvd {p : ℕ} {ks : List ℕ} (h : ∀ k ∈ ks, p ∣ k) : p ∣ recordGcd ks := by
  induction ks with
  | nil => simp [recordGcd]
  | cons a l ih =>
      have hla : p ∣ a := h a (List.mem_cons_self ..)
      have hl : ∀ k ∈ l, p ∣ k := fun k hk => h k (List.mem_cons_of_mem _ hk)
      exact Nat.dvd_gcd hla (ih hl)

theorem recordEstimate_dvd {ks : List ℕ} {r : ℕ} (hr : 0 < r) : recordEstimate ks r ∣ r := by
  induction ks with
  | nil => simp [recordEstimate]
  | cons a l ih =>
      exact Nat.lcm_dvd (recovered_dvd hr) ih

theorem recovered_dvd_recordEstimate {k : ℕ} {ks : List ℕ} {r : ℕ} (hk : k ∈ ks) :
    recovered k r ∣ recordEstimate ks r := by
  induction ks with
  | nil => cases hk
  | cons a l ih =>
      rcases List.mem_cons.mp hk with rfl | hmem
      · exact Nat.dvd_lcm_left _ _
      · exact (ih hmem).trans (Nat.dvd_lcm_right _ _)





/-! ## Two samples suffice -/




open QubitTrade in
theorem solution{r : ℕ} {ks : List ℕ} (hr : 0 < r)
    (h : Nat.gcd (recordGcd ks) r = 1) : recordEstimate ks r = r := by
  obtain ⟨c, hc⟩ := recordEstimate_dvd (ks := ks) hr
  rcases eq_or_ne c 1 with hc1 | hc1
  · rw [hc1, mul_one] at hc; exact hc.symm
  · exfalso
    obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hc1
    obtain ⟨c', hc'⟩ := hpc
    have key : ∀ k ∈ ks, p ∣ Nat.gcd k r := by
      intro k hk
      obtain ⟨e, he⟩ := recovered_dvd_recordEstimate (k := k) (r := r) hk
      have hgr : Nat.gcd k r ∣ r := Nat.gcd_dvd_right _ _
      have hgpos : 0 < Nat.gcd k r := Nat.pos_of_dvd_of_pos hgr hr
      have hrec : recovered k r = r / Nat.gcd k r := recovered_eq hr
      have hdpos : 0 < r / Nat.gcd k r := Nat.div_pos (Nat.le_of_dvd hr hgr) hgpos
      have hrg : (r / Nat.gcd k r) * Nat.gcd k r = r := Nat.div_mul_cancel hgr
      have hmain : (r / Nat.gcd k r) * Nat.gcd k r
          = (r / Nat.gcd k r) * (e * (p * c')) := by
        calc (r / Nat.gcd k r) * Nat.gcd k r = r := hrg
          _ = recordEstimate ks r * c := hc
          _ = (r / Nat.gcd k r) * e * (p * c') := by rw [he, hrec, hc']
          _ = (r / Nat.gcd k r) * (e * (p * c')) := by ring
      have hgeq : Nat.gcd k r = e * (p * c') := Nat.eq_of_mul_eq_mul_left hdpos hmain
      exact ⟨e * c', by rw [hgeq]; ring⟩
    have hks : ∀ k ∈ ks, p ∣ k := fun k hk => (key k hk).trans (Nat.gcd_dvd_left _ _)
    have hpr : p ∣ r := by
      rw [hc, hc']
      exact ⟨recordEstimate ks r * c', by ring⟩
    have hfin : p ∣ Nat.gcd (recordGcd ks) r := Nat.dvd_gcd (recordGcd_dvd hks) hpr
    rw [h] at hfin
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one hfin)
