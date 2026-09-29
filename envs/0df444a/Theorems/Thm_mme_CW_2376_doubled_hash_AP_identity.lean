-- Prove2me | Theorems.Thm_mme_CW_2376_doubled_hash_AP_identity
-- name    : mme_CW_2376_doubled_hash_AP_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:55:50.736807+00:00
-- url     : https://prove2.me/theorems/6a928af7-00d2-459f-9b81-b4b75f3d8e21
-- title:
--   Supported CW 2.376 profile hashes form an arithmetic progression
-- statement:
--   Let $x,y,z$ be three five-grade profile addresses, and suppose the mixed address formed from mode zero of $x$, mode one of $y$, and mode two of $z$ is coordinatewise supported. For arbitrary affine weights in any commutative semiring, their doubled CW hashes obey
--
--   $$
--   H_X^{(2)}(x)+H_Y^{(2)}(y)=2H_Z^{(2)}(z).
--   $$
--
--   This is the exact algebraic kernel of the outer Salem--Spencer pruning. It follows coordinatewise from $I_j+J_j+K_j=4$ and makes no counting, probability, or collision-deletion assertion.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), outer square-profile hashes on journal p. 268 and progression identity (6) on pp. 259--260; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Tactic.Ring
import Definitions.Def_mme_CW_2376_hash_arithmetic

open MME BigOperators

theorem mme_CW_2376_doubled_hash_AP_identity
    {R : Type} [CommSemiring R] {m : ℕ}
    (b0 : R) (w : Fin (cw2376ProfileLength m) → R)
    (x y z : CW2376ProfileAddress m)
    (hsupp : CW2376CoordinatewiseSupported
      (cw2376MixedAddress x y z)) :
    cw2376DoubledXHash w (x 0) +
        cw2376DoubledYHash b0 w (y 1) =
      2 * cw2376DoubledZHash b0 w (z 2) := by
  sorry
