-- Prove2me | Theorems.Thm_mme_stothers_general_exact_target_star_degree_le_power100
-- name    : mme_stothers_general_exact_target_star_degree_le_power100
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:35:05.805988+00:00
-- url     : https://prove2.me/theorems/880f8c4e-9a16-486d-a673-7aab16e51228
-- title:
--   Polynomial bound on a general completion star
-- statement:
--   **The completion star of an exact-profile address is polynomially bounded.**
--
--   Fix an integral ten-class profile $\beta$, a scale $m$, a mode $i$, and an address $a$ with the
--   exact joint profile. Fix a second profile $\beta^{*}$ with the same nine-grade marginals whose
--   exact histogram maximizes conditional entropy among all $45$-cell histograms with those marginals.
--   Then
--
--   $$\#\{b\ \text{marginal-supported} : b_i = a_i\} \;\le\; \bigl(6(N+1)\bigr)^{100}\,D_*(\beta^{*}),
--   \qquad N = 3Dm.$$
--
--   In words: fixing one mode word of an address pins down all but polynomially many multiples of a
--   single star degree -- the one belonging to the maximum-entropy profile on the marginal fibre, not
--   to $\beta$ itself. This is the bound the outer hash consumes, and it is where the two profiles part
--   company: the target count is $V\,D_*(\beta)$ while the star degree is $\mathrm{poly}\cdot
--   D_*(\beta^{*})$, so the retained family carries the ratio
--   $D_*(\beta)/D_*(\beta^{*}) = (\mathcal E(\beta^{*})/\mathcal E(\beta))^{N}$ up to polynomial
--   factors -- exactly the combination loss of Equation (3.4), which is $1$ precisely when $\beta$ is
--   itself the maximum-entropy profile on its fibre.
--
--   The proof splits the star by realized histogram: there are at most $(N+1)^{45}$ histograms and each
--   fibre has at most $\bigl(6(N+1)\bigr)^{45}D_*(\beta^{*})$ elements, and the two polynomial factors
--   combine into $\bigl(6(N+1)\bigr)^{100}$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4), and Lemma 5.2; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_exact_target_star_degree_le_power100
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j = MME.StothersFourth.genMarginalBaseCount base j)
    (hcond : ∀ k : MME.StothersFourth.GenHashJointMultiplicityTable,
      (∀ l : Fin 3, ∀ j : Fin 9,
        (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 l = j},
          k sigma.1) = MME.StothersFourth.genMarginalCount base m j) →
      ∀ i : Fin 3,
      (∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
            (k sigma.1 : ℝ) / (MME.StothersFourth.genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
            (MME.StothersFourth.genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ)))
    (i : Fin 3)
    (a : {a : MME.StothersFourth.GenMarginalSupportedAddress base m //
      MME.StothersFourth.GenHasExactJointProfile a}) :
    Nat.card {b : MME.StothersFourth.GenMarginalSupportedAddress base m // b.1 i = a.1.1 i} ≤
      (6 * (MME.StothersFourth.genOuterLength base m + 1)) ^ 100 *
        MME.StothersFourth.genHashTargetStarDegree bstar m := by
  sorry
