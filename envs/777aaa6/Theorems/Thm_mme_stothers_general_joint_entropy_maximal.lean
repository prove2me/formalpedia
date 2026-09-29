-- Prove2me | Theorems.Thm_mme_stothers_general_joint_entropy_maximal
-- name    : mme_stothers_general_joint_entropy_maximal
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:54:22.674534+00:00
-- url     : https://prove2.me/theorems/f35e0215-b90d-45d1-8ed1-44b23284213c
-- title:
--   Stationary profiles maximize entropy on their fibre
-- statement:
--   **Every stationary integral profile maximizes entropy on its own marginal fibre.**
--
--   Let $\beta^{*}$ be a strictly positive integral ten-class profile whose normalized version
--   $a_i = \beta^{*}_i/D$ satisfies the two stationarity equations of $\mathcal N$,
--
--   $$a_3 a_8^2 = a_5 a_6 a_{10}, \qquad a_4 a_8 a_9 = a_5 a_7 a_{10}$$
--
--   (in the journal's one-based class order). Let $\tau$ be the induced distribution on the $45$
--   supported ordered grade triples, i.e. $\tau_\sigma = a_{r(\sigma)}/3$ where $r(\sigma)$ is the
--   Table-1 class of $\sigma$. Then for every probability distribution $\rho$ on the same $45$ triples
--   with the same three grade marginals,
--
--   $$H(\rho)\;\le\;H(\tau).$$
--
--   No permutation symmetry is assumed of the competitor $\rho$: the comparison is over *all* ordered
--   distributions on the fibre, not only class-constant ones.
--
--   The mechanism is the Gibbs variational principle. The stationarity equations say exactly that
--   $\log a$ is an affine function of the nine-grade statistics: there are potentials
--   $\lambda_0,\dots,\lambda_8$ with $\log \tau_\sigma = c + \lambda_{\sigma_1} + \lambda_{\sigma_2} +
--   \lambda_{\sigma_3}$ for every supported $\sigma$. Any distribution with the same marginals therefore
--   has the same expected log-likelihood under $\tau$, and non-negativity of relative entropy gives
--   $H(\rho)\le H(\tau)$. The two stationarity equations are precisely the two consistency conditions
--   that make the ten class logarithms expressible through nine potentials, one per grade.
--
--   This is the profile-parametric form of the published fixed-witness entropy maximality, and it is the
--   input the general Theorem 5.3 chain needs: it identifies which profile controls the completion-star
--   degree on a given marginal fibre.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Equation (5.2) and Lemma 5.2, with the stationarity equations of A. J. Stothers, On the Complexity of Matrix Multiplication, PhD thesis, University of Edinburgh, 2010, Chapter 4.2, pp. 78-79; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_joint_entropy_maximal
    (bstar : Fin 10 → ℕ) (hpos : ∀ r, 0 < bstar r)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    let Omega :=
      {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}
    let target : Omega → ℝ := fun sigma ↦
      (MME.StothersFourth.genJointMultiplicity bstar 1 sigma.1 : ℝ) /
        (MME.StothersFourth.genOuterLength bstar 1 : ℝ)
    ∀ rho : Omega → ℝ,
      (∀ sigma, 0 ≤ rho sigma) →
      (∑ sigma, rho sigma) = 1 →
      (∀ s : Fin 3, ∀ j : Fin 9,
        mme_modern_marginal (fun sigma : Omega ↦ sigma.1 s) rho j =
          mme_modern_marginal
            (fun sigma : Omega ↦ sigma.1 s) target j) →
      mme_modern_entropyBits rho ≤ mme_modern_entropyBits target := by
  sorry
