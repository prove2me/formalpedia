-- Prove2me | solution 1 for AsymmetricExponent.pow_bijective_iff_eulerGap_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:26:15.360406+00:00
-- url     : https://prove2.me/submissions/9d0bc04e-677c-413d-84fd-a2f25995f5ad

-- Sol generated from Cryptography/AsymmetricExponent/FermatLiars.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core
import Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars
import Theorems.Thm_AsymmetricExponent_card_fermatLiars

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
    Function.Bijective (fun u : (ZMod (p * q))ˣ => u ^ (p * q - 1)) ↔ eulerGap p q = 1 := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hcount := card_fermatLiars (p := p) (q := q) hpq
  constructor
  · intro hbij
    have hsub : Subsingleton {u : (ZMod (p * q))ˣ // u ^ (p * q - 1) = 1} := by
      refine ⟨fun x y => ?_⟩
      have : (x : (ZMod (p * q))ˣ) = y := by
        apply hbij.1
        simp only
        rw [x.2, y.2]
      exact Subtype.ext this
    have hne : Nonempty {u : (ZMod (p * q))ˣ // u ^ (p * q - 1) = 1} := ⟨⟨1, one_pow _⟩⟩
    have : Nat.card {u : (ZMod (p * q))ˣ // u ^ (p * q - 1) = 1} = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, hne⟩
    rw [hcount] at this
    nlinarith [this]
  · intro hg
    rw [hg] at hcount
    have hsub : Subsingleton {u : (ZMod (p * q))ˣ // u ^ (p * q - 1) = 1} :=
      (Nat.card_eq_one_iff_unique.mp (by simpa using hcount)).1
    have hinj : Function.Injective (fun u : (ZMod (p * q))ˣ => u ^ (p * q - 1)) := by
      have : Function.Injective (powMonoidHom (p * q - 1) : (ZMod (p * q))ˣ →* (ZMod (p * q))ˣ) := by
        refine (injective_iff_map_eq_one _).mpr (fun a ha => ?_)
        have ha' : a ^ (p * q - 1) = 1 := by simpa using ha
        have := hsub.allEq (⟨a, ha'⟩ : {u : (ZMod (p * q))ˣ // u ^ (p * q - 1) = 1})
          ⟨1, one_pow _⟩
        exact congrArg Subtype.val this
      simpa [powMonoidHom] using this
    exact Finite.injective_iff_bijective.mp hinj
