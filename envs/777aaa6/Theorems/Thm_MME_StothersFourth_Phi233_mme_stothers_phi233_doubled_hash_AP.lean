-- Prove2me | Theorems.Thm_MME_StothersFourth_Phi233_mme_stothers_phi233_doubled_hash_AP
-- name    : MME.StothersFourth.Phi233.mme_stothers_phi233_doubled_hash_AP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:23:06.63502+00:00
-- url     : https://prove2.me/theorems/96179ae4-4308-4349-a312-e8a603f5b5c9
-- title:
--   Five-grade affine hash arithmetic-progression identity
-- statement:
--   For every supported five-grade Phi233 address and every coordinate-weight word over a commutative ring, the doubled X and Y hashes and complementary Z hash satisfy $$H_X(x)+H_Y(y)=2H_Z(z).$$ The identity follows coordinatewise from the square-grading support equation $x+y+z=4$ and is the algebraic input to Salem--Spencer pruning.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 5, pp. 356-360 and 365-367; arithmetic-progression hashing of five-grade addresses.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

open BigOperators

set_option autoImplicit false

namespace MME.StothersFourth.Phi233

theorem mme_stothers_phi233_doubled_hash_AP
    {R : Type} [CommRing R] {N : ℕ}
    (b : R) (w : Fin (2 * N) → R)
    (x : ProfileAddress N) (hsupp : CoordinatewiseSupported x) :
    doubledXHash b w (x 0) + doubledYHash b w (x 1) =
      2 * doubledZHash b w (x 2) := by
  sorry

end MME.StothersFourth.Phi233
