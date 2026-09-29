-- Prove2me | solution 1 for mme_stothers_phi233_distinct_mode_code_difference_has_nonzero_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:36:21.27597+00:00
-- url     : https://prove2.me/submissions/39c74e7a-1380-4cfb-866b-aac3d860c658

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
import Theorems.Thm_mme_stothers_phi233_cyclic_hash_mode_code_injective

open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (e f : CyclicAmbientEdge N alpha beta gamma delta) (i : Fin 3)
    (hne : cyclicModeWord e i ≠ cyclicModeWord f i) :
    ∃ r : Fin 3, ∃ j : Fin (2 * N),
      cyclicHashModeCode p N i (cyclicModeWord e i) r j -
        cyclicHashModeCode p N i (cyclicModeWord f i) r j ≠ 0 := by
  have hcode : cyclicHashModeCode p N i (cyclicModeWord e i) ≠
      cyclicHashModeCode p N i (cyclicModeWord f i) := by
    intro h
    exact hne (mme_stothers_phi233_cyclic_hash_mode_code_injective hp i h)
  by_contra h
  push_neg at h
  apply hcode
  funext r j
  exact sub_eq_zero.mp (h r j)
