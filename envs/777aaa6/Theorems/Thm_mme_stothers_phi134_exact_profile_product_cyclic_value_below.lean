-- Prove2me | Theorems.Thm_mme_stothers_phi134_exact_profile_product_cyclic_value_below
-- name    : mme_stothers_phi134_exact_profile_product_cyclic_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:30:45.026725+00:00
-- url     : https://prove2.me/theorems/a4ee36f9-051c-481f-b5da-3cd45483ee3d
-- title:
--   Exact-profile cyclic value of the Davie--Stothers phi_134 block
-- statement:
--   Let $2\leq 3\tau$ and consider an exact $\Phi_{1,3,4}$ profile with multiplicities $(\alpha,\beta,\gamma,\delta,\delta,\gamma,\beta,\alpha)$ on the eight fine fourth-power components. For every nonnegative $W$ strictly below $$ L^{2\beta+2\gamma} E^{2\alpha+2\beta+4\delta} H^{2\gamma}, $$ the cyclic symmetrization of the associated Kronecker product has $\tau$-value at least $W$. Here $E,H,L$ are the $q=6$ elementary, high, and coupled endpoints used in Davie--Stothers Lemma 5.1(iii). This packages the algebraic value contribution of one exact profile independently of the later hashing and entropy estimates.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi134_profile_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter
open MME.StothersFourth.Phi134

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_exact_profile_product_cyclic_value_below
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (alpha beta gamma delta : ℕ)
    (W : ℝ) (hW : 0 ≤ W)
    (hWB :
      W <
        MME.StothersFourth.L 6 tau ^ (2 * beta + 2 * gamma) *
        MME.StothersFourth.E 6 tau ^
          (2 * alpha + 2 * beta + 4 * delta) *
        MME.StothersFourth.H 6 tau ^ (2 * gamma)) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kronFin 8 (fun r ↦
          (MME.StothersFourth.Phi134.componentObj K 6 r).kronPow
            (MME.StothersFourth.Phi134.profileMultiplicity
              alpha beta gamma delta r)))) tau W := by
  sorry
