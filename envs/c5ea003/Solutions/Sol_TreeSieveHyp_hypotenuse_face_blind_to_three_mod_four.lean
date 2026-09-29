-- Prove2me | solution 1 for TreeSieveHyp.hypotenuse_face_blind_to_three_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:03:16.939585+00:00
-- url     : https://prove2.me/submissions/ca21aa9c-8a29-415d-b86c-da7278f3647f

-- Sol generated from Bridges/TreeSieveHypotenuseFace.lean
import Mathlib
import Definitions.Def_Bridges_TreeSieveHypotenuseFace
import Definitions.Def_Bridges_TreeSieveLottery
import Theorems.Thm_TreeSieve_bergOf_pyth
import Theorems.Thm_TreeSieveHyp_bergOf_prim
import Theorems.Thm_TreeSieveHyp_prime_dvd_hyp_one_mod_four

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



/-- Every prime divisor of a Berggren-tree hypotenuse is `1 mod 4`. -/
theorem berg_hyp_prime_one_mod_four (w : List (Fin 3)) {p : ℕ} (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ (bergOf w).2.2) : p % 4 = 1 :=
  prime_dvd_hyp_one_mod_four (bergOf_pyth w) (bergOf_prim w) hp hdvd

/-! ## Consequence: zero winning tickets on `3 mod 4` moduli -/





/-! ## Sharpness: the obstruction is specific to the hypotenuse face -/




open TreeSieveHyp in
theorem solution(w : List (Fin 3)) (N : ℕ)
    (h3 : ∀ p : ℕ, p.Prime → p ∣ N → p % 4 = 3) :
    Int.gcd (bergOf w).2.2 (N : ℤ) = 1 := by
  by_contra hg
  obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hg
  have hrc : (r : ℤ) ∣ (bergOf w).2.2 :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hrg) (Int.gcd_dvd_left _ _)
  have hrN : r ∣ N := by
    have : (r : ℤ) ∣ (N : ℤ) :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hrg) (Int.gcd_dvd_right _ _)
    exact_mod_cast this
  have h1 := berg_hyp_prime_one_mod_four w hr hrc
  have h2 := h3 r hr hrN
  omega
