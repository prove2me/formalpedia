-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_hash_mode_code_injective
-- name    : mme_CW_q6_type2_cyclic_hash_mode_code_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:24:23.219125+00:00
-- url     : https://prove2.me/theorems/e01f519d-edc7-4f08-aa23-43633e103dc7
-- title:
--   Injectivity of every cyclic q=6 type-2 hash coefficient code
-- statement:
--   Let $p\ge 7$ be prime. In each of the three cyclic modes, the coefficient code of the combined q=6 type-2 affine hash is injective on mode words. Thus two distinct mode words differ in at least one modular hash coefficient, providing the nonconstant linear equation required by the collision-fiber bound.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; nondegeneracy of the cyclic hash coefficients.

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code

open MME

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_hash_mode_code_injective
    {p N : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (i : Fin 3) :
    Function.Injective (cwQ6Type2CyclicHashModeCode p N i) := by
  sorry
