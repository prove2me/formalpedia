-- Prove2me | Theorems.Thm_mme_stothers_phi134_exact_profile_card
-- name    : mme_stothers_phi134_exact_profile_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:12:26.764156+00:00
-- url     : https://prove2.me/theorems/54855147-a3bb-419e-9bc5-8d2da2d3075c
-- title:
--   Exact cardinality of a symmetric Phi134 profile
-- statement:
--   Let the eight ordered patterns of the $\phi_{134}$ constituent occur with symmetric multiplicities
--
--   $$(\alpha,\beta,\gamma,\delta,\delta,\gamma,\beta,\alpha),\qquad \alpha+\beta+\gamma+\delta=N.$$
--
--   Then the number of exact three-mode addresses of length $2N$ with this joint profile is
--
--   $$\frac{(2N)!}{\prod_{r=0}^{7}m_r!},$$
--
--   where $m$ is the displayed multiplicity vector.  The address type includes both the supported-pattern condition and the three prescribed marginals; the result shows that those marginals impose no additional count once the exact joint profile is fixed.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), printed p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi134_profile_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi134_exact_profile_card
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    Nat.card
        (MME.StothersFourth.Phi134.ExactProfileAddress
          N alpha beta gamma delta) =
      (2 * N).factorial /
        ∏ r : Fin 8,
          (MME.StothersFourth.Phi134.profileMultiplicity
            alpha beta gamma delta r).factorial := by
  sorry
