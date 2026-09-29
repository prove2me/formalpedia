-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_profile_product_cyclic_value_below
-- name    : mme_stothers_phi233_exact_profile_product_cyclic_value_below
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-07T02:28:25.015717+00:00
-- url     : https://prove2.me/theorems/90243f6a-b8bb-403f-93b8-86c8c56470db
-- title:
--   Exact-profile product value for exceptional phi_233
-- statement:
--   At $q=6$, let $T_r$ be the ten source-faithful component tensors of an exact $\varphi_{233}$ profile, with endpoints
--
--   $$
--   (EH, HL, EH, E^2, L^2, L^2, E^2, EH, HL, EH)
--   $$
--
--   in the source order $013,022,031,103,112,121,130,202,211,220$, and let $m_r$ be the corresponding exact-profile multiplicities. Then the cyclic symmetrization of
--
--   $$
--   \bigotimes_{r} T_r^{\otimes m_r}
--   $$
--
--   attains every nonnegative cyclic $\tau$-value strictly below the endpoint product $\prod_r v_r^{m_r}$. This is the common-power profile value required by the isolated kept-family extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), exceptional phi_233 component product.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_stothers_phi233_component_cyclic_value_below
import Theorems.Thm_mme_cyclic_kronFin_multiplicities_of_each_strict_below_product

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_exact_profile_product_cyclic_value_below
    {K : Type u} [Field K] (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (alpha beta gamma delta : ℕ)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        ∏ r : Fin 10,
          (![MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau] :
                Fin 10 → ℝ) r ^
            MME.StothersFourth.Phi233.profileMultiplicity
              alpha beta gamma delta r) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kronFin 10 (fun r ↦
          (MME.StothersFourth.Phi233.componentObj K 6 r).kronPow
            (MME.StothersFourth.Phi233.profileMultiplicity
              alpha beta gamma delta r)))) tau V := by
  sorry
