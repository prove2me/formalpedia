-- Prove2me | Theorems.Thm_gpy_goodPair_iff_local_of_products
-- name    : gpy_goodPair_iff_local_of_products
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:56:52.037146+00:00
-- url     : https://prove2.me/theorems/a598ccd1-3fc7-4ada-9661-9e221030fea7
-- title:
--   Good-pair factorization over the lcm of the products
-- statement:
--   For a fiber pair with products D and E squarefree, a pair (d, e) is good at a coordinate i if and only if at every prime p dividing lcm D E, all coordinates whose lcm is divisible by p have congruent shifts modulo p, and no such coordinate's shift is congruent to h i modulo p. Formalization Note: goodness is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_goodPair_iff_local_of_products {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    {D E : ℕ} (hD : ∏ j, d j = D) (hE : ∏ j, e j = E)
    (hsqD : Squarefree D) (hsqE : Squarefree E) :
    (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ↔
      ∀ p, Nat.Prime p → p ∣ Nat.lcm D E →
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ∀ j', p ∣ Nat.lcm (d j') (e j') →
          h j ≡ h j' [MOD p]) ∧
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ¬ h i ≡ h j [MOD p]) := by sorry
