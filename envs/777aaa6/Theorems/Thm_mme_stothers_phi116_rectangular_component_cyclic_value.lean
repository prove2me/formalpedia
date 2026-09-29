-- Prove2me | Theorems.Thm_mme_stothers_phi116_rectangular_component_cyclic_value
-- name    : mme_stothers_phi116_rectangular_component_cyclic_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:48:30.102817+00:00
-- url     : https://prove2.me/theorems/8d93cabf-2fcc-4b26-8163-e1689e585266
-- title:
--   Exact cyclic tau-value of the rectangular phi_116 component
-- statement:
--   The cyclic symmetrization of the rectangular fine component $\langle12,1,12\rangle$ has tau-value at least $$E(6,\tau)^2=12^{6\tau}.$$ Indeed it restricts to $\langle144,144,144\rangle$, whose elementary matrix-product tau-weight is $(144^3)^\tau$. This is the exact rectangular factor in the Davie--Stothers class-$116$ two-type profile.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21; cyclic matrix-multiplication tensor identity.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_rectangular_component_cyclic_value
    {K : Type u} [Field K] (tau : ℝ) :
    HasTauValueAtLeast (cyclicSymmetrization (MMObj K 12 1 12)) tau
      (MME.StothersFourth.E 6 tau ^ (2 : ℕ)) := by
  sorry
