-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_hash_mode_code_has_nonzero_coefficient
-- name    : mme_CW_q6_type2_cyclic_hash_mode_code_has_nonzero_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:41:40.172355+00:00
-- url     : https://prove2.me/theorems/e852c664-6588-4fbb-80da-4bbcba7948c6
-- title:
--   A pivot coefficient for every exact cyclic q=6 type-2 edge
-- statement:
--   Let $p\ge 7$ be prime and let $N>0$. For every exact cyclic q=6 type-2 edge and each of its three modes, at least one coordinate of the modular hash coefficient code is nonzero. Hence the edge's linear hash form has a pivot coordinate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; nonconstant exact-address hash form.

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code

open MME

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_hash_mode_code_has_nonzero_coefficient
    {p N L G : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hN : 0 < N)
    (e : CWQ6Type2CyclicEdge N L G) (i : Fin 3) :
    ∃ r : Fin 3, ∃ j : Fin (2 * N),
      cwQ6Type2CyclicHashModeCode p N i
        (cwQ6Type2CyclicModeWord e i) r j ≠ 0 := by
  sorry
