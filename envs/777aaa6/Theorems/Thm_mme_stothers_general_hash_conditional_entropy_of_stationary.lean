-- Prove2me | Theorems.Thm_mme_stothers_general_hash_conditional_entropy_of_stationary
-- name    : mme_stothers_general_hash_conditional_entropy_of_stationary
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T04:58:31.528596+00:00
-- url     : https://prove2.me/theorems/e76d2d3b-afee-47df-ac2a-a63298ce2eb7
-- title:
--   Conditional entropy maximality of a stationary partner profile
-- statement:
--   **A stationary partner profile maximises every mode-conditional entropy, at every scale.**
--
--   Let $\beta$ and $\beta^{*}$ be strictly positive integral ten-class profiles with the same nine-grade marginals, $Q\beta^{*} = Q\beta$, and suppose the normalised profile $b = \beta^{*}/D$ is a stationary point of the Davie--Stothers programme, i.e. $b \in \mathcal N$: it lies in the simplex $\mathcal Z$ and satisfies the two multiplicative stationarity relations
--
--   $$b_2\, b_7^{2} = b_4\, b_5\, b_9, \qquad b_3\, b_7\, b_8 = b_4\, b_6\, b_9 .$$
--
--   Then for every scale $m$, every $45$-cell histogram $k$ on the marginal fibre of $\beta$ — that is, every $k$ whose mode-$l$ marginal is the prescribed $(Q\beta)_j m$ for all $l$ and $j$ — and every mode $i$,
--
--   $$\sum_{j=0}^{8} (Q\beta)_j m \; H\!\left(\frac{k(\cdot \mid \sigma_i = j)}{(Q\beta)_j m}\right) \;\le\; \sum_{j=0}^{8} (Q\beta)_j m \; H\!\left(\frac{k^{*}_{\beta^{*},m}(\cdot \mid \sigma_i = j)}{(Q\beta)_j m}\right),$$
--
--   where $k^{*}_{\beta^{*},m}$ is the exact joint histogram of $\beta^{*}$ at scale $m$ and $H$ is entropy in bits.
--
--   This is the hypothesis that drives the star-degree comparison in the hashing step: the number of ways to complete one mode word to a full address is controlled by these conditional entropies, so a stationary partner profile bounds the star degree of every competing histogram on the same marginal fibre.
--
--   Two features are worth isolating.  First, the bound holds *at every scale*, because both the target histogram and the address length are homogeneous of degree one in $m$, so the normalised target does not depend on $m$ at all and the scale-one statement suffices.  Second, stationarity alone is enough: no symmetrisation of the histogram is required, because the two relations above are exactly the consistency conditions that let the ten class logarithms be written through nine grade potentials, and the Gibbs inequality then applies at every stationary profile.
--
--   *Formalization note.* The scale-zero case is degenerate — every marginal count is zero and both sides vanish — and is handled separately.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and the stationarity conditions preceding Equation (3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_hash_conditional_entropy_of_stationary
    (base bstar : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∀ (m : ℕ) (k : MME.StothersFourth.GenHashJointMultiplicityTable),
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
              (MME.StothersFourth.genMarginalCount base m j : ℝ)) := by
  sorry
