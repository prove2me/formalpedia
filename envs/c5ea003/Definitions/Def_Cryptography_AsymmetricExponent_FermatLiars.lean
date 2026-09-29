-- Prove2me | Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars
-- name    : Cryptography_AsymmetricExponent_FermatLiars
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:03:24.199989+00:00
-- url     : https://prove2.me/theorems/e0cc1234-bc22-4c53-a972-26c02ac83242
-- title:
--   Aether Catalog definitions — Cryptography_AsymmetricExponent_FermatLiars
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.AsymmetricExponent.FermatLiars`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/AsymmetricExponent/FermatLiars.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core

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

namespace AsymmetricExponent

open scoped Classical

/-- The **Euler gap** `g = gcd(p-1, q-1)` of a semiprime `N = p*q`. -/
def eulerGap (p q : ℕ) : ℕ := Nat.gcd (p - 1) (q - 1)

/-! ## A gcd criterion for power identities in a finite group -/


/-! ## Component-wise description of the Fermat test -/

variable {p q : ℕ}

/-- The CRT isomorphism on unit groups. -/
noncomputable def crtUnits (h : Nat.Coprime p q) :
    (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits





/-! ## Counting the liars -/




/-! ## Consequences -/








end AsymmetricExponent


