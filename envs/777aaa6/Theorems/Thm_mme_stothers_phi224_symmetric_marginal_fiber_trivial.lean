-- Prove2me | Theorems.Thm_mme_stothers_phi224_symmetric_marginal_fiber_trivial
-- name    : mme_stothers_phi224_symmetric_marginal_fiber_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:43:48.205183+00:00
-- url     : https://prove2.me/theorems/76442c40-4c3d-4014-a990-344e6a357516
-- title:
--   The symmetric phi_224 same-marginal fibre is exact
-- statement:
--   Let a length-$2N$ word in the nine fine $\varphi_{224}$ types have the same three projected marginals as the distinguished profile with parameters $\alpha,\beta,\gamma,\delta$. Suppose its multiplicities are invariant under complementary first-square grades:
--
--   $$
--   k_0=k_8,\qquad k_1=k_7,\qquad k_2=k_6,\qquad k_3=k_5.
--   $$
--
--   Then its full fine multiplicity vector is exactly
--
--   $$
--   (\alpha,\beta,\gamma,\beta,2\delta,\beta,\gamma,\beta,\alpha).
--   $$
--
--   Hence the complement-symmetric subset of the same-marginal fibre is a singleton. This is the integral finite form of the assertion $\Lambda^*_{224,\Gamma}=\{\Gamma\}$ in Davie--Stothers Lemma 5.1(iv); the unrestricted nonsymmetric fibre need not be a singleton.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the type-2 symmetry reduction (3.6) and the assertion that the symmetric phi_224 fibre is trivial in Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_marginal_fiber_parameter

set_option autoImplicit false

theorem mme_stothers_phi224_symmetric_marginal_fiber_trivial
    (N alpha beta gamma delta : ℕ)
    (w : MME.StothersFourth.Phi224.ProfileWord N)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ MME.StothersFourth.Phi224.modeWord w i j = s)).card =
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s)
    (hcomplement :
      let k : Fin 9 → ℕ := fun r ↦
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ w j = r)).card
      k 0 = k 8 ∧ k 1 = k 7 ∧ k 2 = k 6 ∧ k 3 = k 5) :
    ∀ r : Fin 9,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card =
          MME.StothersFourth.Phi224.profileMultiplicity
            alpha beta gamma delta r := by
  sorry
