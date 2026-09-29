-- Prove2me | Theorems.Thm_mme_stothers_general_support_entropy_eq_entropyProduct
-- name    : mme_stothers_general_support_entropy_eq_entropyProduct
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T05:20:48.246082+00:00
-- url     : https://prove2.me/theorems/7b9429bc-74f8-4efb-aec2-fdb11e42a6c8
-- title:
--   Support entropy of a profile equals log 3 minus its entropy product
-- statement:
--   **The Shannon entropy of a profile's grade histogram is $\log 3 - \log E(a)$.**
--
--   Let $\beta$ be a strictly positive integral ten-class profile, $D = \sum_r c_r \beta_r$, and $a = \beta/D$ the normalised profile.  The fourth power $CW_6^{\otimes 4}$ has exactly forty-five supported ordered grade triples $\sigma$ — those with $\sigma_0+\sigma_1+\sigma_2 = 8$ — and the profile assigns to each the multiplicity $\mu_\beta(1,\sigma)$, giving a probability vector on the forty-five cells after dividing by the address length $3D$.
--
--   Then
--
--   $$\ln 2 \; H\!\left(\frac{\mu_\beta(1,\cdot)}{3D}\right) \;=\; \log 3 - \log E(a),
--   \qquad E(a) = \prod_{r=1}^{10} a_r^{\,c_r a_r},$$
--
--   where $H$ is entropy in bits and $E$ is the entropy product of Davie--Stothers.
--
--   This is the dictionary between the two ways the same quantity appears in the argument.  The extraction counts addresses, so it meets the entropy of the forty-five-cell histogram; the rate formula of Equation (5.3) is written multiplicatively through $E$.  The identity says they differ only by the constant $\log 3$, which cancels in every comparison of two profiles on the same marginal fibre.  In particular, for two such profiles $a$ and $b$,
--
--   $$\ln 2 \bigl(H_a - H_b\bigr) \;=\; \log \frac{E(b)}{E(a)},$$
--
--   which is exactly the exponential rate of the star-degree ratio appearing in the general-profile outer capacity.
--
--   *Formalization note.* The combinatorial input is that the ten cyclic classes partition the forty-five supported triples, with the orbit of class $r$ having exactly $3c_r$ elements; both facts are finite checks.  The constant $\log 3$ comes from the normalisation $3D$ rather than $D$, and the cancellation $\sum_r c_r a_r = 1$ is what makes it a constant rather than a profile-dependent term.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3 (Equation (3.4) and the entropy product) and Section 5, Equation (5.3); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_support_entropy_eq_entropyProduct
    (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r) :
    Real.log 2 *
        mme_modern_entropyBits
          (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
            (MME.StothersFourth.genHashTargetJointTable base 1 sigma : ℝ) /
              (MME.StothersFourth.genOuterLength base 1 : ℝ)) =
      Real.log 3 -
        Real.log (MME.StothersFourth.entropyProduct
          (MME.StothersFourth.genProfileB base)) := by
  sorry
