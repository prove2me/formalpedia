-- Prove2me | Theorems.Thm_mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
-- name    : mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:56:41.197819+00:00
-- url     : https://prove2.me/theorems/ab2950d9-f90c-44ad-81a3-09aac8d5bcb2
-- title:
--   Exact fixed-mode degree of the phi_125 profile hypergraph
-- statement:
--   Let α+β+γ=N and fix an exact length-2N φ₁₂₅ profile word. For any mode i, the number of exact profile words with the same mode-i projection is exactly $$ \prod_{s=0}^{4}\frac{m_{i,s}!}{\prod_{r:\,p_i(r)=s} k_r!}, $$ where p_i(r) is the mode-i grade of the supported label r, the k_r are the six exact multiplicities (α,β,γ,γ,β,α), and the m_{i,s} are their projected marginal multiplicities. This gives the exact regular mode degree required in the type-2 collision budget.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Lemma 5.1(ii), printed pp. 359–361 and 364–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_profile_data
import Theorems.Thm_mme_stothers_phi125_exact_iff_marginal_profile
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N)
    (w : MME.StothersFourth.Phi125.ExactProfileWord
      N alpha beta gamma)
    (i : Fin 3) :
    Nat.card
        {v : MME.StothersFourth.Phi125.ExactProfileWord
            N alpha beta gamma //
          MME.StothersFourth.Phi125.modeWord v.1 i =
            MME.StothersFourth.Phi125.modeWord w.1 i} =
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi125.marginalMultiplicity
          N alpha beta gamma i s).factorial /
          ∏ r : {r : Fin 6 //
              MME.StothersFourth.Phi125.pattern r i = s},
            (MME.StothersFourth.Phi125.profileMultiplicity
              alpha beta gamma r.1).factorial := by
  sorry
