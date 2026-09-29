-- Prove2me | solution 1 for AsymmetricExponent.card_fermatLiars
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:17:40.657988+00:00
-- url     : https://prove2.me/submissions/345bf8ae-53da-45a6-ba71-7cb2a4e0afab

-- Sol generated from Cryptography/AsymmetricExponent/FermatLiars.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core
import Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars
import Theorems.Thm_AsymmetricExponent_card_pow_eq_one_units
import Theorems.Thm_AsymmetricExponent_gcd_exp_left
import Theorems.Thm_AsymmetricExponent_gcd_exp_right
import Theorems.Thm_AsymmetricExponent_pow_eq_one_iff_components

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
theorem solution[Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    Nat.card {u : (ZMod (p * q))ˣ // u ^ (p * q - 1) = 1} = (eulerGap p q) ^ 2 := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have e1 : {u : (ZMod (p * q))ˣ // u ^ (p * q - 1) = 1} ≃
      {v : (ZMod p)ˣ × (ZMod q)ˣ // v.1 ^ (p * q - 1) = 1 ∧ v.2 ^ (p * q - 1) = 1} := by
    refine (Equiv.subtypeEquivRight (fun u => pow_eq_one_iff_components hcop u _)).trans ?_
    exact (crtUnits hcop).toEquiv.subtypeEquiv (fun u => Iff.rfl)
  have e2 := e1.trans (Equiv.subtypeProdEquivProd
    (p := fun x : (ZMod p)ˣ => x ^ (p * q - 1) = 1)
    (q := fun y : (ZMod q)ˣ => y ^ (p * q - 1) = 1))
  rw [Nat.card_congr e2, Nat.card_prod, card_pow_eq_one_units p, card_pow_eq_one_units q,
      Nat.gcd_comm (p - 1) (p * q - 1), Nat.gcd_comm (q - 1) (p * q - 1),
      gcd_exp_left hp.pos hq.pos, gcd_exp_right hp.pos hq.pos, eulerGap,
      Nat.gcd_comm (q - 1) (p - 1), sq]
