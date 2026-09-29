-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_exact_edge_card
-- name    : mme_stothers_phi125_cyclic_exact_edge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:12:31.272824+00:00
-- url     : https://prove2.me/theorems/88ca5126-9142-4e56-bcb6-92eb45f52476
-- title:
--   Exact cardinality of the cyclic phi_125 target
-- statement:
--   Let α+β+γ=N and let the six φ₁₂₅ multiplicities be (α,β,γ,γ,β,α). The cyclic type-2 target is the product of three exact profile-word families, so its cardinality is $$\left(\frac{(2N)!}{\prod_{r=0}^{5}m_r!}\right)^3.$$ This supplies the exact target-size factor used in the finite hashing argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(ii), cyclic type-2 profile count; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_profile_data
import Theorems.Thm_mme_stothers_phi125_exact_profile_card

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_exact_edge_card
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N) :
    Nat.card
        (MME.StothersFourth.Phi125.CyclicExactEdge
          N alpha beta gamma) =
      ((2 * N).factorial /
        ∏ r : Fin 6,
          (MME.StothersFourth.Phi125.profileMultiplicity
            alpha beta gamma r).factorial) ^ (3 : ℕ) := by
  sorry
