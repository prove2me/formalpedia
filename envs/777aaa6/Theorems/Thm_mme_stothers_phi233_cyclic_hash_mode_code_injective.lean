-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_hash_mode_code_injective
-- name    : mme_stothers_phi233_cyclic_hash_mode_code_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:32:31.957738+00:00
-- url     : https://prove2.me/theorems/bc963d73-12c5-41d4-a114-dbc7682cc6dd
-- title:
--   Injectivity of the Phi233 cyclic hash coefficient code
-- statement:
--   Over every prime field of characteristic at least five, the coefficient word assigned to a Phi233 cyclic mode vertex is injective. Thus distinct mode words differ in at least one genuine weight coefficient, which supplies the nonconstant linear equation in the pair-collision fiber estimate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 5, pp. 356-360 and 365-367; nondegeneracy of the affine hash code.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_hash_mode_code_injective
    {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (i : Fin 3) :
    Function.Injective
      (MME.StothersFourth.Phi233.cyclicHashModeCode p N i) := by
  sorry
