-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_star_joint_table_image_card_le
-- name    : MME.StothersFourth.mme_stothers_fixed_star_joint_table_image_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:46:48.508707+00:00
-- url     : https://prove2.me/theorems/62656d7a-8212-4f9f-a287-b0300103e3b0
-- title:
--   Polynomial count of joint tables in a fixed Stothers completion star
-- statement:
--   Let $N$ be the outer address length in the fixed Davie--Stothers profile. Fix any finite family $E$ of marginal-supported outer addresses, an address $a$, and one of the three modes. Among the members of $E$ whose word in that mode equals the corresponding word of $a$, the number of distinct supported $45$-cell joint multiplicity tables is at most
--
--   $$
--   (N+1)^{45}.
--   $$
--
--   Each cell count lies between $0$ and $N$, so this is the standard polynomial method-of-types count. It supplies the outer partition factor in the completion-star estimate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equation (3.4), printed pp. 354--356, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; this is the finite method-of-types count for the 45 supported triples in the fixed Section 5 profile.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_star_joint_table_image_card_le
    (m : ℕ)
    (E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m))
    (a : MME.StothersFourth.FixedMarginalSupportedAddress m) (i : Fin 3) :
    ((E.filter (fun b ↦ b.1 i = a.1 i)).image
      MME.StothersFourth.fixedHashJointTable).card ≤
        (MME.StothersFourth.fixedOuterLength m + 1) ^ 45 := by
  sorry
