-- Prove2me | Theorems.Thm_TreeSieveHyp_prim_step
-- name    : TreeSieveHyp.prim_step
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:58:29.367334+00:00
-- url     : https://prove2.me/theorems/eb7fa1c4-72a2-43f9-bfbe-5b0fec968ef6
-- title:
--   Each Berggren move preserves primitivity.
-- statement:
--   Each Berggren move preserves primitivity.
--
--   ```lean
--   theorem TreeSieveHyp.prim_step(i : Fin 3) {t : Triple} (hpy : t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2)
--       (h : Prim t) : Prim (step i t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TreeSieveHypotenuseFace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TreeSieveHypotenuseFace.lean#L63

-- Thm stub generated from Bridges/TreeSieveHypotenuseFace.lean
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

theorem TreeSieveHyp.prim_step(i : Fin 3) {t : Triple} (hpy : t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2)
    (h : Prim t) : Prim (step i t) := by sorry
