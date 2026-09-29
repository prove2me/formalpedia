-- Prove2me | solution 1 for TreeSieveHyp.prime_dvd_hyp_one_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:01:10.56942+00:00
-- url     : https://prove2.me/submissions/1d4a97e0-8918-43a3-8d5e-977a64e08e96

-- Sol generated from Bridges/TreeSieveHypotenuseFace.lean
import Mathlib
import Definitions.Def_Bridges_TreeSieveHypotenuseFace
import Definitions.Def_Bridges_TreeSieveLottery

/-!
# The hypotenuse face of the Berggren tree is blind to `3 mod 4` primes

The tree-sieve experiments measured a real but modest smoothness advantage of
Berggren-tree values over random integers (`7.31×`, against a naive `~44×`
prediction).  This file identifies the exact arithmetic reason — and shows that
the same structure is a *fatal* restriction for factoring.

Every node of the Berggren tree is a **primitive** Pythagorean triple
(`bergOf_prim`), and every prime divisor of the hypotenuse of a primitive triple
is `≡ 1 mod 4` (`prime_dvd_hyp_one_mod_four`).  So the hypotenuse values of the
tree are supported on the half of the primes congruent to `1 mod 4`: that is
where the observed smoothness boost comes from (the effective factor base is a
density-`1/2` subset of the primes, and hypotenuse values are never divisible by
`2, 3, 7, 11, 19, 23, …`).

The price is `hypotenuse_face_blind_to_three_mod_four`: for a modulus `N` all of
whose prime factors are `≡ 3 mod 4` — for example `N = p * q` with
`p ≡ q ≡ 3 mod 4` — the gcd of *any* tree hypotenuse with `N` is `1`.  The
lottery of `Catalog.Bridges.TreeSieveLottery` does not merely have a small
winning probability on this class of moduli: it has **no winning tickets at
all**, uniformly over the whole infinite tree.

Main results:

* `bergOf_prim` — every tree node is a primitive triple.
* `prime_dvd_hyp_one_mod_four` — prime divisors of hypotenuses of primitive
  triples are `1 mod 4`.
* `berg_hyp_prime_one_mod_four` — the same for every node of the tree.
* `hypotenuse_face_blind_to_three_mod_four` — zero success probability on
  `3 mod 4` moduli.
* `hypotenuse_face_blind_semiprime` — the concrete semiprime corollary.
-/

open TreeSieveHyp

open TreeSieve

/-! ## Primitivity is a tree invariant -/







/-! ## Prime divisors of a primitive hypotenuse are `1 mod 4` -/

/-- The hypotenuse of a primitive Pythagorean triple is odd. -/
theorem hyp_odd {a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b)) : ¬ (2 : ℤ) ∣ c := by
  rintro ⟨m, rfl⟩
  rcases Int.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;>
    rcases Int.even_or_odd b with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · exact hprim ⟨⟨k, by ring⟩, ⟨l, by ring⟩⟩
  · have h4 : (4 : ℤ) * (m * m - k * k - l * l - l) = 1 := by linear_combination -hpy
    omega
  · have h4 : (4 : ℤ) * (m * m - k * k - k - l * l) = 1 := by linear_combination -hpy
    omega
  · have h4 : (4 : ℤ) * (m * m - k * k - k - l * l - l) = 2 := by linear_combination -hpy
    omega



/-! ## Consequence: zero winning tickets on `3 mod 4` moduli -/





/-! ## Sharpness: the obstruction is specific to the hypotenuse face -/




open TreeSieveHyp in
theorem solution{a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ r : ℕ, r.Prime → ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b))
    {p : ℕ} (hp : p.Prime) (hdvd : (p : ℤ) ∣ c) : p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hyp_odd hpy (fun h => hprim 2 Nat.prime_two (by exact_mod_cast h)) (by exact_mod_cast hdvd)
  have hab : (p : ℤ) ∣ a ^ 2 + b ^ 2 := by
    rw [hpy]; exact Dvd.dvd.pow hdvd (by norm_num)
  have hbne : ¬ (p : ℤ) ∣ b := by
    intro hb
    have hb2 : (p : ℤ) ∣ b ^ 2 := Dvd.dvd.pow hb (by norm_num)
    have hpa : (p : ℤ) ∣ a ^ 2 := by
      have hrw : a ^ 2 = (a ^ 2 + b ^ 2) - b ^ 2 := by ring
      rw [hrw]; exact dvd_sub hab hb2
    have hrp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact hprim p hp ⟨hrp.dvd_of_dvd_pow hpa, hb⟩
  have h0 : ((a : ZMod p)) ^ 2 + ((b : ZMod p)) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + b ^ 2) p).mpr hab
    push_cast at this
    exact this
  have hbz : (b : ZMod p) ≠ 0 := fun h =>
    hbne ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(a : ZMod p) * (b : ZMod p)⁻¹, ?_⟩
    field_simp
    linear_combination -h0
  have h3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  have := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  omega
