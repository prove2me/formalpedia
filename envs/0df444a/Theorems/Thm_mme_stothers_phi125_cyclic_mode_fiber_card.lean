-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_mode_fiber_card
-- name    : mme_stothers_phi125_cyclic_mode_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:14:47.612716+00:00
-- url     : https://prove2.me/theorems/f17e578b-33cd-483a-be03-2a7783a72ecd
-- title:
--   Exact uniform cyclic mode degree for phi_125
-- statement:
--   For an exact symmetric φ₁₂₅ profile with α+β+γ=N, let D_t be the exact number of profile words having a fixed mode-t word, namely $$D_t=\prod_{s=0}^{4}\frac{m_{t,s}!}{\prod_{r:\,\operatorname{pattern}(r)_t=s}k_r!}.$$ Every fibre of any of the three cyclic vertex maps then has exactly $$D_0D_1D_2$$ elements. This is the uniform target degree used in the type-2 Salem–Spencer collision budget.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Lemma 5.1(ii), exact type-2 mode degree; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_profile_data
import Theorems.Thm_mme_stothers_phi125_fixed_mode_exact_profile_fiber_card

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_mode_fiber_card
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N)
    (e : MME.StothersFourth.Phi125.CyclicExactEdge
      N alpha beta gamma)
    (i : Fin 3) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi125.marginalMultiplicity
          N alpha beta gamma t s).factorial /
          ∏ r : {r : Fin 6 //
              MME.StothersFourth.Phi125.pattern r t = s},
            (MME.StothersFourth.Phi125.profileMultiplicity
              alpha beta gamma r.1).factorial
    Nat.card
        {f : MME.StothersFourth.Phi125.CyclicExactEdge
            N alpha beta gamma //
          MME.StothersFourth.Phi125.cyclicModeWord f i =
            MME.StothersFourth.Phi125.cyclicModeWord e i} =
      D 0 * (D 1 * D 2) := by
  sorry
