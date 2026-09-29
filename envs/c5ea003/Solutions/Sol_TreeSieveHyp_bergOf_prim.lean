-- Prove2me | solution 1 for TreeSieveHyp.bergOf_prim
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:21:58.900257+00:00
-- url     : https://prove2.me/submissions/96c2637a-6868-4bf5-be23-401b570e9cb5

-- Sol generated from Bridges/TreeSieveHypotenuseFace.lean
import Mathlib
import Definitions.Def_Bridges_TreeSieveHypotenuseFace
import Definitions.Def_Bridges_TreeSieveLottery
import Theorems.Thm_TreeSieve_step_pyth
import Theorems.Thm_TreeSieveHyp_prim_step

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


theorem prim_root : Prim (3, 4, 5) := by
  rintro r hr ⟨h3, h4⟩
  have h1 : (r : ℤ) ∣ 1 := by simpa using dvd_sub h4 h3
  have h2 : r ∣ 1 := by exact_mod_cast h1
  have := Nat.le_of_dvd Nat.one_pos h2
  have := hr.two_le
  omega



theorem bergFrom_prim (w : List (Fin 3)) {t : Triple}
    (hpy : t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2) (h : Prim t) : Prim (bergFrom t w) := by
  induction w generalizing t with
  | nil => simpa [bergFrom] using h
  | cons i w ih => exact ih (step_pyth i t hpy) (prim_step i hpy h)


/-! ## Prime divisors of a primitive hypotenuse are `1 mod 4` -/




/-! ## Consequence: zero winning tickets on `3 mod 4` moduli -/





/-! ## Sharpness: the obstruction is specific to the hypotenuse face -/




open TreeSieveHyp in
theorem solution(w : List (Fin 3)) : Prim (bergOf w) :=
  bergFrom_prim w (by norm_num) prim_root
