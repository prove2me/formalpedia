-- Prove2me | Theorems.Thm_mme_stothers_phi224_profile_histogram_class_card
-- name    : mme_stothers_phi224_profile_histogram_class_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:23:34.712892+00:00
-- url     : https://prove2.me/theorems/745edb55-b468-46d2-96d2-f90fc666420c
-- title:
--   Multinomial size of a compatible phi_224 histogram class
-- statement:
--   Let $k=(k_0,\ldots,k_8)$ be a nonnegative integral histogram of total mass $2N$ on the nine fine $\varphi_{224}$ types. Assume that projecting $k$ through each of the three grade maps gives the prescribed Davie--Stothers marginal histograms. Then the number of same-marginal words having exactly the fine histogram $k$ is
--
--   $$
--   \frac{(2N)!}{\prod_{r=0}^{8} k_r!}.
--   $$
--
--   This identifies each compatible joint-profile stratum with an ordinary multinomial word class. It is the total-cardinality half of the regular-fibre factorization used in the type-2 hashing argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), equations (3.5)--(3.6) and the type-2 counting argument in Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mme_stothers_phi224_profile_histogram_class_card
    (N alpha beta gamma delta : ℕ) (k : Fin 9 → ℕ)
    (hkTotal : (∑ r : Fin 9, k r) = 2 * N)
    (hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r l = s}, k r.1) =
        MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta l s) :
    Nat.card
        {b : MME.StothersFourth.Phi224.MarginalProfileWord
            N alpha beta gamma delta //
          ∀ r : Fin 9,
            Fintype.card {j : Fin (2 * N) // b.1 j = r} = k r} =
      (2 * N).factorial / ∏ r : Fin 9, (k r).factorial := by
  sorry
