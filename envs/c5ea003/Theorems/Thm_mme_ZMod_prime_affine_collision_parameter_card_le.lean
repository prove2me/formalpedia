-- Prove2me | Theorems.Thm_mme_ZMod_prime_affine_collision_parameter_card_le
-- name    : mme_ZMod_prime_affine_collision_parameter_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:48:01.635348+00:00
-- url     : https://prove2.me/theorems/dc46d871-5136-4718-bdba-a25d7664d398
-- title:
--   A nontrivial linear collision with a fixed affine offset has at most $p^n$ parameters
-- statement:
--   Let $p$ be prime.  Consider affine-hash parameters consisting of a weight vector $w\in(\mathbb Z/p\mathbb Z)^{n+1}$ and an offset $b\in\mathbb Z/p\mathbb Z$.  If retained parameters must satisfy a nonzero linear equation $L(w)=0$ and the offset is uniquely prescribed as $b=f(w)$, then—even after imposing any additional predicate—the number of parameter pairs is at most
--
--   $$
--   p^n.
--   $$
--
--   This is the exact collision-counting kernel for affine Coppersmith--Winograd hashes: the nontrivial linear equation and the determined offset together cost two factors of $p$ from the $p^{n+2}$ parameter space.
-- source:
--   Elementary finite-field counting; used in the affine-hash collision deletion of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_fiber_card

open BigOperators

theorem mme_ZMod_prime_affine_collision_parameter_card_le
    {p n : ℕ} [hp : Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (offset : (Fin (n + 1) → ZMod p) → ZMod p)
    (P : ((Fin (n + 1) → ZMod p) × ZMod p) → Prop)
    [DecidablePred P] :
    ((Finset.univ.filter
      (fun q : (Fin (n + 1) → ZMod p) × ZMod p =>
        (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1 ∧ P q)).card) ≤
      p ^ n := by
  sorry
