-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_joint_entropy_maximal
-- name    : MME.StothersFourth.mme_stothers_fixed_joint_entropy_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:22:16.502223+00:00
-- url     : https://prove2.me/theorems/c3799c3f-620e-4ab8-be9b-7adb36c1e166
-- title:
--   Maximum entropy of the fixed Stothers 45-cell distribution
-- statement:
--   Let $\Omega=\{(i,j,k)\in\{0,\ldots,8\}^3:i+j+k=8\}$ be the 45 ordered fourth-power constituent types. Normalize the exact fixed Stothers joint multiplicities at scale one to obtain a probability distribution $p_*$ on $\Omega$. For every nonnegative probability distribution $\rho$ on $\Omega$ whose three nine-grade coordinate marginals agree with those of $p_*$,
--
--   $$
--   H_2(\rho)\le H_2(p_*).
--   $$
--
--   Thus the fixed stationary Stothers distribution is a global Shannon-entropy maximizer over the entire ordered 45-cell marginal fiber; no permutation-invariance assumption is imposed on the competing distribution. This is the entropy form needed to compare arbitrary completion tables in the outer-hash extraction.
--
--   **Formalization Note** The exact distribution is defined by the published integer profile `fixedJointMultiplicity 1`, normalized by `fixedOuterLength 1`. Entropy and marginals use the platform's reusable finite-distribution definitions.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Equation (5.2) and Lemma 5.2, printed pp. 367–368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; stationary equations as derived in A. J. Stothers, On the Complexity of Matrix Multiplication, PhD thesis, 2010, Chapter 4.2, printed pp. 78–79, https://era.ed.ac.uk/bitstream/handle/1842/4734/Stothers2010.pdf. The theorem is the ordered-45-cell entropy consequence of the same additive stationarity certificate.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_modern_entropy_data

open BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_joint_entropy_maximal :
    let Omega :=
      {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}
    let target : Omega → ℝ := fun sigma ↦
      (MME.StothersFourth.fixedJointMultiplicity 1 sigma.1 : ℝ) /
        (MME.StothersFourth.fixedOuterLength 1 : ℝ)
    ∀ rho : Omega → ℝ,
      (∀ sigma, 0 ≤ rho sigma) →
      (∑ sigma, rho sigma) = 1 →
      (∀ s : Fin 3, ∀ j : Fin 9,
        mme_modern_marginal (fun sigma : Omega ↦ sigma.1 s) rho j =
          mme_modern_marginal
            (fun sigma : Omega ↦ sigma.1 s) target j) →
      mme_modern_entropyBits rho ≤ mme_modern_entropyBits target := by
  sorry
