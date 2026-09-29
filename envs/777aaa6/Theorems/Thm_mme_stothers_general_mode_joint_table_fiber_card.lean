-- Prove2me | Theorems.Thm_mme_stothers_general_mode_joint_table_fiber_card
-- name    : mme_stothers_general_mode_joint_table_fiber_card
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:25:27.000293+00:00
-- url     : https://prove2.me/theorems/9bf47a9d-6d63-422f-b92a-a2a45cc3f99d
-- title:
--   Completions of one mode word with a prescribed histogram
-- statement:
--   **Completions of one mode word with a prescribed joint histogram.**
--
--   Fix an integral ten-class profile $\beta$, a scale $m$, a marginal-supported address $a$ of length
--   $N=3Dm$, a mode $i$, and a $45$-cell histogram $k$ whose three grade marginals are the prescribed
--   ones, $\sum_{\sigma:\sigma_l=j} k_\sigma = M_j$ for every mode $l$ and grade $j$. Then the number
--   of marginal-supported addresses that agree with $a$ on the $i$-th mode word and have joint
--   histogram exactly $k$ is
--
--   $$\frac{\prod_{j} M_j!}{\prod_{\sigma} k_\sigma!}.$$
--
--   Fixing the $i$-th word freezes, for each grade $j$, which $M_j$ positions carry that grade in mode
--   $i$; a completion is then a choice, independently over the nine grades, of how to distribute those
--   positions among the supported triples lying over $j$ in mode $i$, with the multiplicities
--   prescribed by $k$. That is a product of nine multinomial coefficients, and regrouping the
--   denominators over all $45$ cells gives the displayed quotient. The marginal hypothesis on $k$ is
--   exactly what makes each of those nine multinomials well posed, and also what forces the resulting
--   address to be marginally regular in the other two modes.
--
--   This quotient is the *star degree at* $k$; comparing it with the star degree at the
--   maximum-entropy histogram on the same marginal fibre is what produces the combination loss of
--   Equation (3.4).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_mode_joint_table_fiber_card
    (base : Fin 10 → ℕ) (m : ℕ)
    (a : MME.StothersFourth.GenMarginalSupportedAddress base m) (i : Fin 3)
    (k : MME.StothersFourth.GenHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
          sigma.1 l = j}, k sigma.1) =
        MME.StothersFourth.genMarginalCount base m j) :
    Nat.card
        {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
          b.1 i = a.1 i ∧
            MME.StothersFourth.genHashJointTable b = k} =
      (∏ j : Fin 9,
          (MME.StothersFourth.genMarginalCount base m j).factorial) /
        ∏ sigma : MME.StothersFourth.GenHashSupportTriple,
          (k sigma).factorial := by
  sorry
