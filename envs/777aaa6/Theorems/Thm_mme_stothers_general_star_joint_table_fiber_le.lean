-- Prove2me | Theorems.Thm_mme_stothers_general_star_joint_table_fiber_le
-- name    : mme_stothers_general_star_joint_table_fiber_le
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:34:54.966118+00:00
-- url     : https://prove2.me/theorems/df4c1aa1-070d-48d9-a855-c6260d318610
-- title:
--   Histogram fibres of a completion star
-- statement:
--   **Each histogram fibre of a completion star is polynomially bounded by the reference star degree.**
--
--   Fix an integral ten-class profile $\beta$, a scale $m$, an ambient family $E$ of
--   marginal-supported addresses, an address $a$, and a mode $i$; and fix a second profile
--   $\beta^{*}$ with the same nine-grade marginals such that every $45$-cell histogram with the
--   prescribed marginals has conditional entropy at most that of $\beta^{*}$'s exact histogram. Then
--   for every histogram $k$ realized on the star of $a$ at $i$,
--
--   $$\#\{b \in E : b_i = a_i,\ \text{histogram}(b)=k\} \;\le\; \bigl(6(N+1)\bigr)^{45}\,D_*(\beta^{*}),$$
--
--   with $N = 3Dm$.
--
--   A histogram realized on the star automatically has the prescribed marginals -- that is forced by
--   the marginal regularity of the addresses realizing it -- so the fibre is counted exactly by the
--   completion quotient $\prod_j M_j!/\prod_\sigma k_\sigma!$, and the entropy hypothesis bounds that
--   quotient by $\bigl(6(N+1)\bigr)^{45}D_*(\beta^{*})$ uniformly in $k$. Summing over the
--   polynomially many realized histograms then bounds the whole star.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4), and Lemma 5.2; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_star_joint_table_fiber_le
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hcond : ∀ k : MME.StothersFourth.GenHashJointMultiplicityTable,
      (∀ l : Fin 3, ∀ j : Fin 9,
        (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
          sigma.1 l = j}, k sigma.1) =
          MME.StothersFourth.genMarginalCount base m j) →
      ∀ i : Fin 3,
      (∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = j} ↦
            (k sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = j} ↦
            (MME.StothersFourth.genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ)))
    (E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m))
    (a : MME.StothersFourth.GenMarginalSupportedAddress base m) (i : Fin 3)
    (k : MME.StothersFourth.GenHashJointMultiplicityTable)
    (hk : k ∈ (E.filter (fun b ↦ b.1 i = a.1 i)).image
      MME.StothersFourth.genHashJointTable) :
    ((E.filter (fun b ↦ b.1 i = a.1 i)).filter
      (fun b ↦ MME.StothersFourth.genHashJointTable b = k)).card ≤
        (6 * (MME.StothersFourth.genOuterLength base m + 1)) ^ 45 *
          MME.StothersFourth.genHashTargetStarDegree bstar m := by
  sorry
