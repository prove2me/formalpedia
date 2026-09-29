-- Prove2me | solution 1 for AsymmetricExponent.exists_fermat_witness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:22:34.890074+00:00
-- url     : https://prove2.me/submissions/b25d4fed-5dcb-4ce7-9b07-c80b4724e937

-- Sol generated from Cryptography/AsymmetricExponent/FermatLiars.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core
import Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars
import Theorems.Thm_AsymmetricExponent_card_fermatLiars
import Theorems.Thm_AsymmetricExponent_eulerGap_lt

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


theorem card_units_semiprime (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.card (ZMod (p * q))ˣ = (p - 1) * (q - 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.pos.ne' hq.pos.ne'⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_mul hcop,
      Nat.totient_prime hp, Nat.totient_prime hq]

/-- **At most half of the residues are Fermat liars**, so the Fermat test on a
semiprime with distinct factors succeeds with probability at least `1/2`. -/
theorem fermatLiar_density_le_half [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    2 * Nat.card {u : (ZMod (p * q))ˣ // u ^ (p * q - 1) = 1} ≤ Nat.card (ZMod (p * q))ˣ := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  rw [card_fermatLiars hpq, card_units_semiprime hp hq hpq]
  exact eulerGap_lt hp hq hpq






open AsymmetricExponent in
theorem solution[Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    ∃ u : (ZMod (p * q))ˣ, u ^ (p * q - 1) ≠ 1 := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  by_contra hcon
  push_neg at hcon
  have hall : Nat.card {u : (ZMod (p * q))ˣ // u ^ (p * q - 1) = 1}
      = Nat.card (ZMod (p * q))ˣ :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hcon)
  have hlt := fermatLiar_density_le_half (p := p) (q := q) hpq
  rw [hall, card_units_semiprime hp hq hpq] at hlt
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hpos : 0 < (p - 1) * (q - 1) := Nat.mul_pos (by omega) (by omega)
  omega
