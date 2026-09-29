-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_exact_target_subtype_nat_card
-- name    : MME.StothersFourth.mme_stothers_fixed_exact_target_subtype_nat_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:17:37.156146+00:00
-- url     : https://prove2.me/theorems/8a0ed05c-5434-4a2e-bb1e-b82592c2216e
-- title:
--   Exact cardinality of the fixed Stothers target-address family
-- statement:
--   Let $N$ be the outer length at scale $m$, and let $k^*_\sigma$ be the prescribed multiplicity of each of the $45$ supported joint types. The number of marginal-supported outer addresses having exactly this target joint profile is
--
--   $$
--   \frac{N!}{\prod_{\sigma\in\Omega}k^*_\sigma!}.
--   $$
--
--   The count is the multinomial number of words over the supported joint types with their prescribed histogram. Exact-profile words automatically have the required support and marginals, so this is also the cardinality of the target subtype in the full marginal universe.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Equations (3.3)--(3.4) and the exact Section 5 profile, printed pp. 354--356 and 367--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; this is the exact multinomial enumeration of the prescribed type class.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_exact_target_subtype_nat_card
    (m : ℕ) :
    Nat.card
        {a : MME.StothersFourth.FixedMarginalSupportedAddress m //
          MME.StothersFourth.FixedHasExactJointProfile a} =
      (MME.StothersFourth.fixedOuterLength m).factorial /
        ∏ sigma : MME.StothersFourth.FixedHashSupportTriple,
          (MME.StothersFourth.fixedHashTargetJointTable m sigma).factorial := by
  sorry
