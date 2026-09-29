-- Prove2me | Theorems.Thm_mme_stothers_phi233_elementary_component_cyclic_values
-- name    : mme_stothers_phi233_elementary_component_cyclic_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:20:08.423283+00:00
-- url     : https://prove2.me/theorems/d8aa89ef-e258-4e19-9f58-a8a909997b99
-- title:
--   Exact cyclic values of the elementary $\Phi_{233}$ components
-- statement:
--   For the exceptional $\Phi_{233}$ profile at $q=6$, the representative elementary component $\langle 1,q^2+2,2q\rangle$ has exact cyclic $\tau$-value $EH$, while the representative $\langle 2q,2q,1\rangle$ has exact cyclic $\tau$-value $E^2$. Here $E=(2q)^{3\tau}$ and $H=(q^2+2)^{3\tau}$. The cyclic symmetrization turns a rectangular matrix-multiplication tensor into the square tensor whose side is the product of its three dimensions.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), elementary factors in the exceptional phi_233 calculation, Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_CW_coupled_value

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_elementary_component_cyclic_values
    {K : Type u} [Field K] (tau : ℝ) :
    HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.Phi233.componentObj K 6 0)) tau
        (MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau) ∧
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.Phi233.componentObj K 6 3)) tau
        (MME.StothersFourth.E 6 tau ^ (2 : ℕ)) := by
  sorry
