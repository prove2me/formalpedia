-- Prove2me | Theorems.Thm_mme_stothers_phi224_marginal_fiber_parameter
-- name    : mme_stothers_phi224_marginal_fiber_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:25:43.838015+00:00
-- url     : https://prove2.me/theorems/842b5c8c-a1bb-401c-a633-8e0fdd651b75
-- title:
--   The phi_224 same-marginal fibre has one imbalance parameter
-- statement:
--   Fix a length-$2N$ word in the nine fine $\varphi_{224}$ types, and suppose its three projected grade histograms equal the Davie--Stothers marginals. If $k_r$ is the number of occurrences of fine type $r$, then the marginal equations force
--
--   $$
--   k_0=k_8=\alpha,\qquad k_4=2\delta,\qquad k_1=k_5,\qquad k_3=k_7,
--   $$
--
--   $$
--   k_1+k_3=2\beta,\qquad k_1+k_2=\beta+\gamma,\qquad k_3+k_6=\beta+\gamma.
--   $$
--
--   Thus the ambient same-marginal fibre is governed by a single off-diagonal imbalance (for example $k_1-\beta$). This is the exact source-faithful replacement for the false assertion that the entire marginal fibre is a singleton; only the symmetric distinguished profile is unique in the source argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the phi_224 same-marginal fibre in Lemma 5.1(iv), pp. 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_marginal_fiber_parameter
    (N alpha beta gamma delta : ℕ)
    (w : MME.StothersFourth.Phi224.ProfileWord N)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ MME.StothersFourth.Phi224.modeWord w i j = s)).card =
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s) :
    let k : Fin 9 → ℕ := fun r ↦
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card
    k 0 = alpha ∧ k 8 = alpha ∧ k 4 = 2 * delta ∧
      k 1 = k 5 ∧ k 3 = k 7 ∧
      k 1 + k 3 = 2 * beta ∧
      k 1 + k 2 = beta + gamma ∧
      k 3 + k 6 = beta + gamma := by
  sorry
