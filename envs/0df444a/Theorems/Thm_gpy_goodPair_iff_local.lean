-- Prove2me | Theorems.Thm_gpy_goodPair_iff_local
-- name    : gpy_goodPair_iff_local
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:49:33.622865+00:00
-- url     : https://prove2.me/theorems/8417abaa-675d-49d0-b6cc-2aa8c20c8808
-- title:
--   Good pairs factorize prime by prime over the combined modulus
-- statement:
--   For squarefree products, a pair (d, e) is good at a coordinate i — some witness w satisfies lcm (d j) (e j) ∣ w + h j at every coordinate and w + h i is coprime to the combined modulus L — if and only if at every prime p dividing L, all coordinates whose lcm is divisible by p have congruent shifts modulo p, and no such coordinate's shift is congruent to h i modulo p. Admissibility is not a hypothesis. Formalization Note: goodness is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_goodPair_iff_local {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hsqd : Squarefree (∏ j, d j)) (hsqe : Squarefree (∏ j, e j)) :
    (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ↔
      ∀ p, Nat.Prime p →
        p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) →
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ∀ j', p ∣ Nat.lcm (d j') (e j') →
          h j ≡ h j' [MOD p]) ∧
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ¬ h i ≡ h j [MOD p]) := by sorry
