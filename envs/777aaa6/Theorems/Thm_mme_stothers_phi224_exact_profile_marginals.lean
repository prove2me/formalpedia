-- Prove2me | Theorems.Thm_mme_stothers_phi224_exact_profile_marginals
-- name    : mme_stothers_phi224_exact_profile_marginals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:25:30.225547+00:00
-- url     : https://prove2.me/theorems/24071158-f8ff-4e84-b65d-48e12b8b6710
-- title:
--   Exact phi_224 profile length and projected marginals
-- statement:
--   Let $\alpha,\beta,\gamma,\delta$ be nonnegative integers satisfying $\alpha+2\beta+\gamma+\delta=N$. The nine fine labels of $\varphi_{224}$ are pairwise distinct, and their exact symmetric multiplicities
--
--   $$
--   (\alpha,\beta,\gamma,\beta,2\delta,\beta,\gamma,\beta,\alpha)
--   $$
--
--   sum to $2N$. Every word with this exact profile has the projected histograms printed in Lemma 5.1(iv):
--
--   $$
--   Q_1\Gamma=Q_2\Gamma=(\alpha+\beta+\gamma, 2\beta+2\delta, \alpha+\beta+\gamma, 0, 0),
--   $$
--
--   $$
--   Q_3\Gamma=(\alpha, 2\beta, 2\gamma+2\delta, 2\beta, \alpha).
--   $$
--
--   This is the exact finite bookkeeping needed before the type-2 fibre counts, affine hashing, and retained-block realization can be instantiated for the literal $\varphi_{224}$ constituent.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iv), displayed phi_224 profile and marginals on pp. 365–366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_exact_profile_marginals
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    Function.Injective MME.StothersFourth.Phi224.pattern ∧
    (∑ r : Fin 9,
      MME.StothersFourth.Phi224.profileMultiplicity
        alpha beta gamma delta r) = 2 * N ∧
    ∀ w : MME.StothersFourth.Phi224.ProfileWord N,
      (∀ r : Fin 9,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ w j = r)).card =
            MME.StothersFourth.Phi224.profileMultiplicity
              alpha beta gamma delta r) →
      ∀ i : Fin 3, ∀ s : Fin 5,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦
            MME.StothersFourth.Phi224.modeWord w i j = s)).card =
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s := by
  sorry
