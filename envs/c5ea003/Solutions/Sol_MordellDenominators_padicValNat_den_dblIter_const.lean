-- Prove2me | solution 1 for MordellDenominators.padicValNat_den_dblIter_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:32:07.638101+00:00
-- url     : https://prove2.me/submissions/c09dac8e-f002-4632-b5a7-0ab3aab9a1c6

-- Sol generated from Cryptography/MordellDenominators/Valuation.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_dblIter_onCurve
import Theorems.Thm_MordellDenominators_dvd_den_dblIter_of_dvd
import Theorems.Thm_MordellDenominators_padicValNat_dblX_den

/-!
# Exact `ℓ`-adic behaviour of denominators under duplication

`Basic.lean` shows that a prime in a denominator never disappears.  Here we
compute the exact multiplicity, which turns out to be rigid:

* for an **odd** prime `ℓ` in the denominator, duplication *preserves* the
  `ℓ`-adic valuation:
  `padicValNat ℓ (dblX N x).den = padicValNat ℓ x.den`
  (`MordellDenominators.padicValNat_den_dblX_odd`);
* for `ℓ = 2` the valuation increases by exactly `2`
  (`MordellDenominators.padicValNat_den_dblX_two`);
* a good prime `ℓ` *not yet* present enters with the exact valuation
  `2 v_ℓ(num y)` (`MordellDenominators.padicValNat_den_dblX_good`), so it
  enters iff it divides the numerator of the `y`-coordinate
  (`MordellDenominators.good_prime_dvd_den_dblX_iff`).

This is the elementary shadow of the formal-group statement `z(2P) = 2z + …`:
away from the residue characteristic of the multiplier, multiplication by `2`
is an isomorphism of the kernel of reduction, whereas at `ℓ = 2` it strictly
deepens it.  In particular a good prime, once present, occurs with the *same*
exponent forever — the denominators keep broadcasting it.
-/

open MordellDenominators




/-- **Odd primes: duplication preserves the valuation.**  If an odd prime `ℓ`
divides the denominator of `x(P)`, then `x(2P)` has exactly the same `ℓ`-adic
denominator valuation. -/
theorem padicValNat_den_dblX_odd {N : ℤ} {x y : ℚ} (h : OnCurve N x y) {l : ℕ}
    (hl : l.Prime) (hodd : l ≠ 2) (hd : l ∣ x.den) :
    padicValNat l (dblX N x).den = padicValNat l x.den := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h4 : padicValNat l 4 = 0 := by
    refine padicValNat.eq_zero_of_not_dvd ?_
    intro hcon
    have : l ∣ 2 ^ 2 := by simpa using hcon
    exact hodd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow this))
  rw [padicValNat_dblX_den h hl hd, h4, zero_add]







open MordellDenominators in
theorem solution{N : ℤ}
    (hnt : ∀ x y : ℚ, OnCurve N x y → y ≠ 0) {P : ℚ × ℚ}
    (h : OnCurve N P.1 P.2) {l : ℕ} (hl : l.Prime) (hodd : l ≠ 2) {n : ℕ}
    (hd : l ∣ (dblIter N n P).1.den) :
    ∀ m : ℕ, padicValNat l (dblIter N (n + m) P).1.den
      = padicValNat l (dblIter N n P).1.den := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
      have hstep : dblIter N (n + k + 1) P = dbl N (dblIter N (n + k) P) := by
        simp [dblIter, Function.iterate_succ_apply']
      have hsum : n + (k + 1) = n + k + 1 := by ring
      have hdk : l ∣ (dblIter N (n + k) P).1.den :=
        dvd_den_dblIter_of_dvd hnt h hl hd k
      rw [hsum, hstep]
      have := padicValNat_den_dblX_odd (dblIter_onCurve hnt h (n + k)) hl hodd hdk
      simpa [dbl] using this.trans ih
