-- Prove2me | Theorems.Thm_mme_stothers_phi233_component_cyclic_value_below
-- name    : mme_stothers_phi233_component_cyclic_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:30:55.301347+00:00
-- url     : https://prove2.me/theorems/604b5126-3a52-46bd-b666-8686d136b36f
-- title:
--   All ten exceptional $\Phi_{233}$ component values
-- statement:
--   At $q=6$, each of the ten source-faithful component tensors in the exceptional $\Phi_{233}$ profile attains every nonnegative cyclic $\tau$-value strictly below its listed endpoint. In source order $013,022,031,103,112,121,130,202,211,220$, the endpoints are
--
--   $$
--   (EH, HL, EH, E^2, L^2, L^2, E^2, EH, HL, EH).
--   $$
--
--   The $EH$ and $E^2$ entries are elementary matrix-multiplication tensors. The $HL$ and $L^2$ entries combine elementary or coupled Coppersmith--Winograd factors, with cyclic mode rotations transported by tensor isomorphism. The strict formulation preserves the asymptotic nature of the coupled value bound.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), exceptional phi_233 component decomposition and values, Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_component_cyclic_value_below
    {K : Type u} [Field K] (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ (r : Fin 10) (V : ℝ),
      0 ≤ V →
      V < (![MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
        MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
        MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
        MME.StothersFourth.E 6 tau ^ (2 : ℕ),
        MME.StothersFourth.L 6 tau ^ (2 : ℕ),
        MME.StothersFourth.L 6 tau ^ (2 : ℕ),
        MME.StothersFourth.E 6 tau ^ (2 : ℕ),
        MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
        MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
        MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau] :
          Fin 10 → ℝ) r →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.Phi233.componentObj K 6 r)) tau V := by
  sorry
