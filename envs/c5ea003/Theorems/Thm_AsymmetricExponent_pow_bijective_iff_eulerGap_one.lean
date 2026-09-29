-- Prove2me | Theorems.Thm_AsymmetricExponent_pow_bijective_iff_eulerGap_one
-- name    : AsymmetricExponent.pow_bijective_iff_eulerGap_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:33:04.474452+00:00
-- url     : https://prove2.me/theorems/02f3cd69-f4bf-47f2-9e28-dd84420ae6eb
-- title:
--   **The `(N-1)`-power map on units is a bijection exactly when the Euler gap
-- statement:
--   **The `(N-1)`-power map on units is a bijection exactly when the Euler gap
--   is `1`.**
--
--   ```lean
--   theorem AsymmetricExponent.pow_bijective_iff_eulerGap_one[Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
--       Function.Bijective (fun u : (ZMod (p * q))ˣ => u ^ (p * q - 1)) ↔ eulerGap p q = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AsymmetricExponent/FermatLiars.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AsymmetricExponent/FermatLiars.lean#L231

-- Thm stub generated from Cryptography/AsymmetricExponent/FermatLiars.lean
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

theorem AsymmetricExponent.pow_bijective_iff_eulerGap_one[Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    Function.Bijective (fun u : (ZMod (p * q))ˣ => u ^ (p * q - 1)) ↔ eulerGap p q = 1 := by sorry
