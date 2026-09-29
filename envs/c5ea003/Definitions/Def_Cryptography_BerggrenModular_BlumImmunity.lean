-- Prove2me | Definitions.Def_Cryptography_BerggrenModular_BlumImmunity
-- name    : Cryptography_BerggrenModular_BlumImmunity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:09:51.907759+00:00
-- url     : https://prove2.me/theorems/9c081ea0-e1a7-4419-8644-3e955936f619
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenModular_BlumImmunity
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenModular.BlumImmunity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenModular/BlumImmunity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
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

namespace Cryptography
namespace BerggrenModular

/-! ## Primitive Pythagorean triples: the hypotenuse is `1 (mod 4)`-smooth -/





/-! ## Transport to the Berggren tree -/



/-- The natural-number hypotenuse of a node of the Berggren tree. -/
def hypNat (u : List Move) : ℕ := (applyWord u root).2.2.toNat




/-! ## Blindness of the hypotenuse dive -/


/-- A *Blum integer* in the sense used here: a product of two primes, each
`≡ 3 (mod 4)`.  These are exactly the Rabin / Blum–Blum–Shub moduli. -/
def IsBlum (N : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ N = p * q




end BerggrenModular


