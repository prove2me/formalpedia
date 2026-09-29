-- Prove2me | Theorems.Thm_mme_stothers_phi125_exact_profile_card
-- name    : mme_stothers_phi125_exact_profile_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:55:10.108426+00:00
-- url     : https://prove2.me/theorems/513b490c-84a1-4f15-93c3-f63b611309c4
-- title:
--   Exact multinomial count of phi_125 symmetric profiles
-- statement:
--   Let α, β, γ be nonnegative integers with α+β+γ=N. A length-2N φ₁₂₅ profile word has the six prescribed multiplicities (α,β,γ,γ,β,α). The number of such words is exactly $$ \frac{(2N)!}{\prod_{r=0}^{5}m_r!},\qquad (m_0,\ldots,m_5)=(\alpha,\beta,\gamma,\gamma,\beta,\alpha). $$ This is the exact target-family cardinality used in the finite type-2 hashing argument for Davie–Stothers Lemma 5.1(ii).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Lemma 5.1(ii), printed pp. 359–361 and 364–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_profile_data

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi125_exact_profile_card
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N) :
    Nat.card
        (MME.StothersFourth.Phi125.ExactProfileWord
          N alpha beta gamma) =
      (2 * N).factorial /
        ∏ r : Fin 6,
          (MME.StothersFourth.Phi125.profileMultiplicity
            alpha beta gamma r).factorial := by
  sorry
