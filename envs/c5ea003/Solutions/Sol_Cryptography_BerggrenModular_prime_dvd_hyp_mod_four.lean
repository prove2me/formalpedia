-- Prove2me | solution 1 for Cryptography.BerggrenModular.prime_dvd_hyp_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:17:09.348863+00:00
-- url     : https://prove2.me/submissions/9b7af960-dea2-4dbe-9be9-f255003f8374

-- Sol generated from Cryptography/BerggrenModular/BlumImmunity.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_BlumImmunity
import Definitions.Def_Cryptography_BerggrenModular_NullCone

/-!
# The ambient null: the Berggren hypotenuse stream cannot see primes `≡ 3 (mod 4)`

The modular-dynamics experiment (exp 555) reports that the mod-`N` Berggren orbit
*under-samples factor-revealing residues* relative to random Pythagorean points.
This file isolates a hard, exact structural reason for a large part of that
deficit, and proves it.

Every node of the Berggren tree is a **primitive** Pythagorean triple
(`Cryptography.BerggrenModular.NullCone.Prim_applyWord`).  A classical fact —
proved here from scratch — is that the hypotenuse of a primitive Pythagorean
triple has *only* prime divisors `≡ 1 (mod 4)`.  Consequently a "dive" that
inspects `gcd(c, N)` along the tree

* can never expose a prime factor `p ≡ 3 (mod 4)` of `N`, and
* is **completely blind** on Blum integers `N = pq`, `p ≡ q ≡ 3 (mod 4)` — the
  moduli used in Rabin/Blum–Blum–Shub and a positive-density share of RSA-like
  moduli — no matter how deep the traversal goes.

## Main results

* `hyp_not_even` — the hypotenuse of a primitive Pythagorean triple is odd.
* `prime_not_dvd_leg` — a prime dividing the hypotenuse divides neither leg.
* `prime_dvd_hyp_mod_four` — **every prime divisor of the hypotenuse of a
  primitive Pythagorean triple is `≡ 1 (mod 4)`.**
* `berggren_hyp_prime_divisors_one_mod_four` — the same for every node of the
  Berggren tree.
* `berggren_gcd_eq_one_of_all_prime_factors_three_mod_four` — the hypotenuse of
  every node is coprime to any modulus all of whose prime factors are `≡ 3 (4)`.
* `berggren_dive_blind_on_blum` — **Blum-integer immunity**: for `N = p*q` with
  `p ≡ q ≡ 3 (mod 4)` the hypotenuse dive reveals nothing at any depth.
* `berggren_dive_undersamples` — for `N = p*q` with `p ≡ 3 (mod 4)` the only
  factor the dive can ever return is `q`: half of the factor-revealing residues
  are structurally unreachable.
-/

open Cryptography
open BerggrenModular

/-! ## Primitive Pythagorean triples: the hypotenuse is `1 (mod 4)`-smooth -/



/-- The hypotenuse of a primitive Pythagorean triple is odd. -/
theorem hyp_not_even {a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d) : ¬ ((2 : ℤ) ∣ c) := by
  rintro ⟨k, rfl⟩
  rcases Int.even_or_odd a with ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
    rcases Int.even_or_odd b with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have h := hprim 2 ⟨s, by ring⟩ ⟨t, by ring⟩ ⟨k, rfl⟩
    rw [Int.isUnit_iff] at h; omega
  · have h4 : (4 : ℤ) ∣ 1 := ⟨k ^ 2 - s ^ 2 - t ^ 2 - t, by linarith [hpy]⟩
    norm_num at h4
  · have h4 : (4 : ℤ) ∣ 1 := ⟨k ^ 2 - s ^ 2 - s - t ^ 2, by linarith [hpy]⟩
    norm_num at h4
  · have h4 : (4 : ℤ) ∣ 2 := ⟨k ^ 2 - s ^ 2 - s - t ^ 2 - t, by linarith [hpy]⟩
    norm_num at h4

/-- A prime dividing the hypotenuse of a primitive triple divides neither leg. -/
theorem prime_not_dvd_leg {a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d)
    {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ c) : ¬ ((p : ℤ) ∣ a) := by
  intro hda
  have hdb : (p : ℤ) ∣ b := by
    have hb2 : (p : ℤ) ∣ b ^ 2 := by
      have hbe : b ^ 2 = c ^ 2 - a ^ 2 := by linarith
      rw [hbe]
      exact dvd_sub (dvd_pow hd two_ne_zero) (dvd_pow hda two_ne_zero)
    exact Int.Prime.dvd_pow' (by exact_mod_cast hp) hb2
  have hu := hprim p hda hdb hd
  rw [Int.isUnit_iff] at hu
  have := hp.two_le
  omega

/-- Symmetric version: the prime divides neither leg. -/
theorem prime_not_dvd_leg' {a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d)
    {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ c) : ¬ ((p : ℤ) ∣ b) := by
  refine prime_not_dvd_leg (a := b) (b := a) (by linarith) ?_ hp hd
  intro d h1 h2 h3
  exact hprim d h2 h1 h3


/-! ## Transport to the Berggren tree -/







/-! ## Blindness of the hypotenuse dive -/




/-- Non-vacuity of `IsBlum`: `21 = 3·7` is a Blum integer, and the dive is blind
on it at every depth. -/
example : IsBlum 21 := ⟨3, 7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Sharpness: the blindness is caused by the residue `3 (mod 4)`, not by the
search.  For `N = 65 = 5·13` the dive already splits `N` at depth two: the node
`B₃B₂` has hypotenuse `85` and `gcd(85, 65) = 5`. -/
example : hypNat [Move.m3, Move.m2] = 85 := by decide

example : Nat.gcd (hypNat [Move.m3, Move.m2]) 65 = 5 := by decide

/-- Sharpness in the other direction: the `1 (mod 4)` law is a property of the
*hypotenuse* only.  The legs are unconstrained — the node `B₁(3,4,5) = (5,12,13)`
has a leg divisible by `3` — so a leg-based dive is not structurally blind on Blum
moduli.  It is still trial-division-class, by the counting theorems in
`Cryptography.BerggrenModular.TrialDivisionEquivalence`. -/
example : (3 : ℤ) ∣ (applyWord [Move.m1] root).2.1 := by decide




open Cryptography in
theorem solution{a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d)
    {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ c) : p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : p ≠ 2 := by
    rintro rfl
    exact hyp_not_even hpy hprim (by exact_mod_cast hd)
  have hnb : ¬ ((p : ℤ) ∣ b) := prime_not_dvd_leg' hpy hprim hp hd
  have hc0 : ((c : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).2 hd
  have hA : ((a : ZMod p)) ^ 2 + ((b : ZMod p)) ^ 2 = 0 := by
    have h := congrArg (fun z : ℤ => ((z : ZMod p))) hpy
    push_cast at h
    rw [h, hc0]; ring
  have hbne : ((b : ZMod p)) ≠ 0 := fun h => hnb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).1 h)
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(a : ZMod p) * ((b : ZMod p))⁻¹, ?_⟩
    field_simp
    linear_combination -hA
  have h3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 hsq
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two h2)
  omega
