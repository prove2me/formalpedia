-- Prove2me | Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity
-- name    : mme_CW_q6_doubled_hash_AP_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:41:33.407745+00:00
-- url     : https://prove2.me/theorems/d472b81b-4329-44d1-adb8-307da467cb76
-- title:
--   Coupled q=6 address hashes satisfy the progression identity
-- statement:
--   Let $x,y,z$ be three coupled $q=6$ coarse addresses, and suppose the mixed address formed from the first mode of $x$, the second mode of $y$, and the third mode of $z$ is coordinatewise supported. For every choice of affine offset and position weights in any commutative semiring, the doubled hashes obey
--
--   $$
--   h_X(x)+h_Y(y)=2h_Z(z).
--   $$
--
--   This is the exact algebraic kernel of the first Salem–Spencer hash. It follows from the four supported grade triples $(0,0,0)$, $(1,1,1)$, $(0,1,2)$, and $(1,0,2)$, and makes no probabilistic or counting assertion.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), affine hash progression identity (equation (6)) on journal pp. 259–260, invoked for the coupled q=6 first hash on journal p. 271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Tactic.Ring
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open MME BigOperators

theorem mme_CW_q6_doubled_hash_AP_identity
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin (2 * N) → R)
    (x y z : CWQ6CoupledAddress N)
    (hsupp : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress x y z)) :
    cwQ6DoubledXHash b0 w (x 0) +
        cwQ6DoubledYHash b0 w (y 1) =
      2 * cwQ6DoubledZHash b0 w (z 2) := by sorry
