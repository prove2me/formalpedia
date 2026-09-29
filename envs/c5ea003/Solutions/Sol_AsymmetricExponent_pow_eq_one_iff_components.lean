-- Prove2me | solution 1 for AsymmetricExponent.pow_eq_one_iff_components
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:13:59.223059+00:00
-- url     : https://prove2.me/submissions/63519dda-26f8-44c9-8743-073fa659ade8

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
theorem solution(h : Nat.Coprime p q) (u : (ZMod (p * q))ˣ)
    (n : ℕ) :
    u ^ n = 1 ↔ ((crtUnits h u).1 ^ n = 1 ∧ (crtUnits h u).2 ^ n = 1) := by
  constructor
  · intro hu
    have : (crtUnits h) (u ^ n) = 1 := by rw [hu, map_one]
    rw [map_pow] at this
    constructor
    · exact congrArg Prod.fst this
    · exact congrArg Prod.snd this
  · rintro ⟨h1, h2⟩
    have : (crtUnits h) (u ^ n) = 1 := by
      rw [map_pow]
      exact Prod.ext h1 h2
    simpa using (MulEquiv.map_eq_one_iff (crtUnits h)).mp this
