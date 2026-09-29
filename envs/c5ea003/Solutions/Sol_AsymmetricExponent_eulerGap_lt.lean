-- Prove2me | solution 1 for AsymmetricExponent.eulerGap_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:19:15.392195+00:00
-- url     : https://prove2.me/submissions/5abd1cc2-6010-45d7-a4a4-4bdee9e241da

-- Sol generated from Cryptography/AsymmetricExponent/FermatLiars.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core
import Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars

/-!
# The Euler gap governs `a^(N-1) mod N` completely

For a semiprime `N = p*q` the Fermat exponent `N - 1` is, in each CRT
component, congruent to the *other* prime's Fermat exponent (`Core.lean`).
This file draws the consequence that the whole multiplicative behaviour of
`Q(a) = a^(N-1)` is controlled by a single number, the **Euler gap**

  `g = gcd(p-1, q-1)`.

Main results.

* `AsymmetricExponent.fermatLiar_iff_eulerGap` — for every unit `u` mod `N`,
  `u^(N-1) = 1 ↔ u^g = 1`.  The Fermat test modulo a semiprime *is* the
  `g`-th power test: nothing of `p` or `q` beyond `g` is visible.
* `AsymmetricExponent.card_fermatLiars` — there are exactly `g^2` Fermat liars
  modulo `N` (the experimentally measured "reveal density" count).
* `AsymmetricExponent.exists_fermat_witness` — consequently a semiprime with
  distinct prime factors is never a Carmichael number.
* `AsymmetricExponent.fermatLiar_density_le_half` — the liar density is at most
  `1/2`: `2 * g^2 ≤ (p-1) * (q-1)`.
* `AsymmetricExponent.card_range_pow` — the image of the `(N-1)`-power map has
  size `φ(N)/g²`, and
  `AsymmetricExponent.pow_bijective_iff_eulerGap_one` — the map is bijective iff
  `g = 1`.
* `AsymmetricExponent.liarGroupEquiv` — the liar group is isomorphic to
  `(ℤ/g) × (ℤ/g)`: its isomorphism type depends on the factorisation only
  through `g`.
-/

open AsymmetricExponent

open scoped Classical


/-! ## A gcd criterion for power identities in a finite group -/


/-! ## Component-wise description of the Fermat test -/

variable {p q : ℕ}






/-! ## Counting the liars -/




/-! ## Consequences -/









open AsymmetricExponent in
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    2 * (eulerGap p q) ^ 2 ≤ (p - 1) * (q - 1) := by
  have hg1 : eulerGap p q ∣ p - 1 := Nat.gcd_dvd_left _ _
  have hg2 : eulerGap p q ∣ q - 1 := Nat.gcd_dvd_right _ _
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hgpos : 0 < eulerGap p q := Nat.gcd_pos_of_pos_left _ (by omega)
  -- in the smaller-prime direction `g ≤ min (p-1) (q-1)`; in the larger one `2g ≤ max`
  rcases lt_or_gt_of_ne hpq with h | h
  · have hle : eulerGap p q ≤ p - 1 := Nat.le_of_dvd (by omega) hg1
    have hne : eulerGap p q ≠ q - 1 := by
      intro hEq
      have : q - 1 ≤ p - 1 := hEq ▸ hle
      omega
    have hlt : eulerGap p q < q - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hg2) hne
    have h2g : 2 * eulerGap p q ≤ q - 1 := by
      obtain ⟨c, hc⟩ := hg2
      have hc2 : 2 ≤ c := by
        rcases Nat.lt_or_ge c 2 with hc1 | hc1
        · interval_cases c <;> omega
        · exact hc1
      calc 2 * eulerGap p q ≤ c * eulerGap p q := Nat.mul_le_mul_right _ hc2
        _ = q - 1 := by rw [hc]; ring
    calc 2 * (eulerGap p q) ^ 2 = (2 * eulerGap p q) * eulerGap p q := by ring
      _ ≤ (q - 1) * (p - 1) := Nat.mul_le_mul h2g hle
      _ = (p - 1) * (q - 1) := Nat.mul_comm _ _
  · have hle : eulerGap p q ≤ q - 1 := Nat.le_of_dvd (by omega) hg2
    have hne : eulerGap p q ≠ p - 1 := by
      intro hEq
      have : p - 1 ≤ q - 1 := hEq ▸ hle
      omega
    have h2g : 2 * eulerGap p q ≤ p - 1 := by
      obtain ⟨c, hc⟩ := hg1
      have hc2 : 2 ≤ c := by
        rcases Nat.lt_or_ge c 2 with hc1 | hc1
        · interval_cases c <;> omega
        · exact hc1
      calc 2 * eulerGap p q ≤ c * eulerGap p q := Nat.mul_le_mul_right _ hc2
        _ = p - 1 := by rw [hc]; ring
    calc 2 * (eulerGap p q) ^ 2 = (2 * eulerGap p q) * eulerGap p q := by ring
      _ ≤ (p - 1) * (q - 1) := Nat.mul_le_mul h2g hle
