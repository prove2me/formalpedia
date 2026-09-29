-- Prove2me | Theorems.Thm_mme_ZMod_unit_affine_collision_parameter_card_le
-- name    : mme_ZMod_unit_affine_collision_parameter_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:19:52.868669+00:00
-- url     : https://prove2.me/theorems/65109df9-b7dc-4919-8575-824eb5be6d61
-- title:
--   A unit-coefficient collision with fixed affine offset has at most $M^n$ parameters
-- statement:
--   Let $M>0$. Consider affine-hash parameters $(w,b)$ with $w\in(\mathbb Z/M\mathbb Z)^{n+1}$ and $b\in\mathbb Z/M\mathbb Z$. If retained parameters satisfy a linear equation $L(w)=0$ having a unit coefficient and an equation that uniquely prescribes $b$ from $w$, then, even after imposing any additional predicate, their number is at most
--
--   $$
--   M^n.
--   $$
--
--   This is the composite-modulus collision-counting kernel for the Coppersmith--Winograd affine hash.
-- source:
--   Elementary finite abelian-group counting; used in the affine-hash analysis of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib
import Theorems.Thm_mme_ZMod_unit_linear_hash_fiber_card

open BigOperators

theorem mme_ZMod_unit_affine_collision_parameter_card_le
    {M n : ℕ} [NeZero M]
    (c : Fin (n + 1) → ZMod M) (j : Fin (n + 1))
    (hc : IsUnit (c j))
    (offset : (Fin (n + 1) → ZMod M) → ZMod M)
    (P : ((Fin (n + 1) → ZMod M) × ZMod M) → Prop)
    [DecidablePred P] :
    ((Finset.univ.filter
      (fun q : (Fin (n + 1) → ZMod M) × ZMod M =>
        (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1 ∧ P q)).card) ≤
      M ^ n := by
  sorry
