-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_distinct_mode_code_difference_has_nonzero_coefficient
-- name    : mme_CW_q6_type2_cyclic_distinct_mode_code_difference_has_nonzero_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:47:20.518035+00:00
-- url     : https://prove2.me/theorems/5b9c2aaa-66d9-4a2f-ac3d-28d52a0eef15
-- title:
--   A nonzero collision coefficient from distinct cyclic q=6 mode words
-- statement:
--   Let $p\ge 7$ be prime. If two cyclic q=6 type-2 edges have distinct mode words in a specified mode, then the difference of their modular coefficient codes is nonzero in at least one row and tensor-power coordinate. Consequently their simultaneous retention imposes a nonconstant homogeneous linear equation on the hash weights.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; collision nondegeneracy for the cyclic hash.

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Theorems.Thm_mme_CW_q6_type2_cyclic_hash_mode_code_injective

open MME

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_distinct_mode_code_difference_has_nonzero_coefficient
    {p N L G : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e f : CWQ6Type2CyclicEdge N L G) (i : Fin 3)
    (hne : cwQ6Type2CyclicModeWord e i ≠
      cwQ6Type2CyclicModeWord f i) :
    ∃ r : Fin 3, ∃ j : Fin (2 * N),
      cwQ6Type2CyclicHashModeCode p N i
          (cwQ6Type2CyclicModeWord e i) r j -
        cwQ6Type2CyclicHashModeCode p N i
          (cwQ6Type2CyclicModeWord f i) r j ≠ 0 := by
  sorry
