-- Prove2me | Theorems.Thm_mme_stothers_general_mode_conditional_entropy_maximal
-- name    : mme_stothers_general_mode_conditional_entropy_maximal
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:44:24.587373+00:00
-- url     : https://prove2.me/theorems/190758d5-0f4b-4f3a-835b-60fc74d6ceca
-- title:
--   Conditional entropy maximality from joint maximality
-- statement:
--   **Joint entropy maximality implies conditional entropy maximality.**
--
--   Fix an integral ten-class profile $\beta$ with strictly positive counts, a scale $m\ge1$, and a
--   second profile $\beta^{*}$ with the same nine-grade marginals. Suppose the normalized exact
--   histogram $\tau$ of $\beta^{*}$ maximizes Shannon entropy among all probability distributions on
--   the $45$ supported grade triples having its three grade marginals. Then, for every mode $i$ and
--   every integral histogram $k$ with the prescribed marginals $M_j$,
--
--   $$\sum_j M_j\,H\!\left(\frac{k|_j}{M_j}\right)\;\le\;\sum_j M_j\,H\!\left(\frac{\tau|_j}{M_j}\right),$$
--
--   the restrictions being to the supported triples whose $i$-th coordinate is $j$.
--
--   Both sides are $N$ times a conditional entropy $H(\cdot\mid \text{grade in mode } i)$, and by the
--   chain rule each equals $N$ times the joint entropy minus $N$ times the entropy of the mode-$i$
--   marginal. The marginal term is the same on both sides -- that is what the shared-marginal
--   hypothesis buys -- so the conditional comparison is exactly the joint one. Passing from the
--   unconditional to the conditional form is what makes the entropy hypothesis usable by the
--   completion-star count, which works one mode word at a time.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3, and Lemma 5.2; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_mode_conditional_entropy_maximal
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j = MME.StothersFourth.genMarginalBaseCount base j)
    (i : Fin 3)
    (k : MME.StothersFourth.GenHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 l = j},
        k sigma.1) = MME.StothersFourth.genMarginalCount base m j)
    (hjoint : ∀ rho : MME.StothersFourth.GenHashSupportTriple → ℝ,
      (∀ sigma, 0 ≤ rho sigma) →
      (∑ sigma, rho sigma) = 1 →
      (∀ l : Fin 3, ∀ j : Fin 9,
        mme_modern_marginal (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦ sigma.1 l)
            rho j =
          mme_modern_marginal (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦ sigma.1 l)
            (fun sigma ↦ (MME.StothersFourth.genHashTargetJointTable bstar m sigma : ℝ) /
              (MME.StothersFourth.genOuterLength base m : ℝ)) j) →
      mme_modern_entropyBits rho ≤
        mme_modern_entropyBits
          (fun sigma ↦ (MME.StothersFourth.genHashTargetJointTable bstar m sigma : ℝ) /
            (MME.StothersFourth.genOuterLength base m : ℝ))) :
    (∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
      mme_modern_entropyBits
        (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
          (k sigma.1 : ℝ) / (MME.StothersFourth.genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
            (MME.StothersFourth.genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ)) := by
  sorry
