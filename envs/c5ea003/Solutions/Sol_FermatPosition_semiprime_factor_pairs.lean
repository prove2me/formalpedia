-- Prove2me | solution 1 for FermatPosition.semiprime_factor_pairs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:38:13.835482+00:00
-- url     : https://prove2.me/submissions/7598eb56-623f-4acf-9d00-eea7b0a40889

-- Sol generated from NumberTheory/FermatPositionTerminal.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionGeometry
/-
# Square positions of the sieve polynomial: the terminal Fermat position

Third companion to `Catalog/NumberTheory/FermatPositionGeometry.lean`.

Among all positions `j` of the sieve polynomial `v(j) = (b + j)^2 - N` the *square*
positions — those with `v(j)` a perfect square — are exactly the factorizations of `N`.
This is Fermat's method, and it gives the one piece of **exactly known** positional
geometry of the smooth locus, against which any statistical claim about hit positions can
be calibrated.

Main results.

* `sieveVal_eq_sq_iff` : `v(j) = k²` iff `N = (b + j - k)(b + j + k)`.
* `sieveVal_at_mid` : writing `N = s² - d²`, the position `s - b` is a square position
  with value `d²`; for `N = p q` with `p + q = 2s`, `q - p = 2d` this is the *terminal
  Fermat position*.
* `terminal_position_bound` : `2 b (s - b) ≤ d²`, i.e. the terminal position obeys the
  same linear magnitude law `2 b j ≤ v(j)` as every other position.  Balanced semiprimes
  (small `d` relative to `√N`) have their terminal position at small `j`; this is a
  *magnitude* statement, not extra positional structure.
* `semiprime_factor_pairs` : the factorizations of a semiprime.
* `square_position_unique` : the only square positions of a semiprime sieve are the
  trivial one (`b + j - k = 1`) and the terminal Fermat position `2 (b + j) = p + q`.
-/

open FermatPosition








open FermatPosition in
theorem solution{p q u w : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q)
    (h : u * w = p * q) (huw : u ≤ w) : (u = 1 ∧ w = p * q) ∨ (u = p ∧ w = q) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hu : u ∣ p * q := ⟨w, h.symm⟩
  by_cases hpu : p ∣ u
  · obtain ⟨u', rfl⟩ := hpu
    have hq' : u' * w = q := by
      have : p * (u' * w) = p * q := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    have hu'dvd : u' ∣ q := ⟨w, hq'.symm⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq u' hu'dvd) with h1 | h1
    · subst h1
      exact Or.inr ⟨by ring, by simpa using hq'⟩
    · exfalso
      rw [h1] at hq' huw
      have hw : w = 1 := by
        have : q * w = q * 1 := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega) this
      rw [hw] at huw
      nlinarith
  · have hcop : Nat.Coprime p u := (Nat.Prime.coprime_iff_not_dvd hp).2 hpu
    have hudvd : u ∣ q := Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hcop) hu
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq u hudvd) with h1 | h1
    · subst h1
      exact Or.inl ⟨rfl, by simpa using h⟩
    · subst h1
      have hw : w = p := by
        have h5 : u * w = u * p := by rw [h]; ring
        exact Nat.eq_of_mul_eq_mul_left (by omega) h5
      have hup : u = p := le_antisymm (by omega) hpq
      exact Or.inr ⟨hup, by omega⟩
