-- Prove2me | Theorems.Thm_Cryptography_BerggrenModular_prime_not_dvd_leg
-- name    : Cryptography.BerggrenModular.prime_not_dvd_leg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:38:41.905312+00:00
-- url     : https://prove2.me/theorems/13ccafa1-018a-4f87-9650-cdcf0fc2bdd0
-- title:
--   A prime dividing the hypotenuse of a primitive triple divides neither leg.
-- statement:
--   A prime dividing the hypotenuse of a primitive triple divides neither leg.
--
--   ```lean
--   theorem Cryptography.BerggrenModular.prime_not_dvd_leg{a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
--       (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d)
--       {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ c) : ¬ ((p : ℤ) ∣ a) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenModular/BlumImmunity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenModular/BlumImmunity.lean#L58

-- Thm stub generated from Cryptography/BerggrenModular/BlumImmunity.lean
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

theorem Cryptography.BerggrenModular.prime_not_dvd_leg{a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d)
    {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ c) : ¬ ((p : ℤ) ∣ a) := by sorry
