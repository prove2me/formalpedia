-- Prove2me | Theorems.Thm_mme_stothers_phi134_marginals_force_exact_profile
-- name    : mme_stothers_phi134_marginals_force_exact_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:21:09.429722+00:00
-- url     : https://prove2.me/theorems/ec2ecf11-b667-46d8-949c-9dd2f96ef7d1
-- title:
--   The three phi_134 marginals force its exact eight-pattern profile
-- statement:
--   Index the eight supported summands of $\phi_{134}$ by $(004),(013),(022),(031),(103),(112),(121),(130)$. Suppose a length-$2N$ supported address has the three marginal histograms from Davie--Stothers Lemma 5.1(iii): $$ (N,N,0,0,0),\qquad (\alpha+\delta,\beta+\gamma,\beta+\gamma,\alpha+\delta,0),\qquad (\alpha,\beta+\delta,2\gamma,\beta+\delta,\alpha). $$ Then the eight joint multiplicities are necessarily $$ (\alpha,\beta,\gamma,\delta,\delta,\gamma,\beta,\alpha). $$ Hence the same-marginal completion family for $\phi_{134}$ is exactly its prescribed profile family; there is no completion-entropy loss in the ensuing type-2 hash extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), printed p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi134_profile_data

open MME BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_marginals_force_exact_profile
    (N alpha beta gamma delta : ℕ)
    (x : MME.StothersFourth.Phi134.MarginalAddress
      N alpha beta gamma delta) :
    ∀ r : Fin 8,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ MME.StothersFourth.Phi134.addressType x.1 j =
          MME.StothersFourth.Phi134.pattern r)).card =
        MME.StothersFourth.Phi134.profileMultiplicity
          alpha beta gamma delta r := by
  sorry
