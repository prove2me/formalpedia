-- Prove2me | Theorems.Thm_mme_stothers_phi233_distinct_mode_code_difference_has_nonzero_coefficient
-- name    : mme_stothers_phi233_distinct_mode_code_difference_has_nonzero_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:35:16.666744+00:00
-- url     : https://prove2.me/theorems/5701d56f-70f3-42d8-9ec8-21372111df0f
-- title:
--   A distinct Phi233 mode pair has a nonzero hash coefficient difference
-- statement:
--   If two Phi233 ambient edges have different vertices in a fixed mode, then their cyclic hash coefficient words differ at some genuine weight coordinate. Equivalently, the corresponding hash-collision equation contains a nonzero coefficient and hence cuts the state space by a factor of $p$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 5, pp. 356-360 and 365-367; nonconstant pair-collision hash equation.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
import Theorems.Thm_mme_stothers_phi233_cyclic_hash_mode_code_injective

set_option autoImplicit false

theorem mme_stothers_phi233_distinct_mode_code_difference_has_nonzero_coefficient
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (e f : MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta)
    (i : Fin 3)
    (hne : MME.StothersFourth.Phi233.cyclicModeWord e i ≠
      MME.StothersFourth.Phi233.cyclicModeWord f i) :
    ∃ r : Fin 3, ∃ j : Fin (2 * N),
      MME.StothersFourth.Phi233.cyclicHashModeCode p N i
            (MME.StothersFourth.Phi233.cyclicModeWord e i) r j -
          MME.StothersFourth.Phi233.cyclicHashModeCode p N i
            (MME.StothersFourth.Phi233.cyclicModeWord f i) r j ≠ 0 := by
  sorry
