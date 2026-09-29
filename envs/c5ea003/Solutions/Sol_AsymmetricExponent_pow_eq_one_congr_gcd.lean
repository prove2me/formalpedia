-- Prove2me | solution 1 for AsymmetricExponent.pow_eq_one_congr_gcd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:26:16.112704+00:00
-- url     : https://prove2.me/submissions/00dc8844-d58b-428e-a69d-15e3d421c7a7

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
theorem solution{G : Type*} [Group G] [Fintype G] (x : G) {n m : ℕ}
    (h : Nat.gcd n (Fintype.card G) = Nat.gcd m (Fintype.card G)) :
    x ^ n = 1 ↔ x ^ m = 1 := by
  have hcard : orderOf x ∣ Fintype.card G := orderOf_dvd_card
  constructor
  · intro hx
    have hdvd : orderOf x ∣ Nat.gcd n (Fintype.card G) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx) hcard
    rw [h] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp (hdvd.trans (Nat.gcd_dvd_left _ _))
  · intro hx
    have hdvd : orderOf x ∣ Nat.gcd m (Fintype.card G) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx) hcard
    rw [← h] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp (hdvd.trans (Nat.gcd_dvd_left _ _))
