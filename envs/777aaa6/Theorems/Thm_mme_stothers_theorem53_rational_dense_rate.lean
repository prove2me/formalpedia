-- Prove2me | Theorems.Thm_mme_stothers_theorem53_rational_dense_rate
-- name    : mme_stothers_theorem53_rational_dense_rate
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-10T05:55:35.270846+00:00
-- url     : https://prove2.me/theorems/24828d6f-ef32-4337-a9ca-0ccbcf2634dd
-- title:
--   Rational profile pairs approach any admissible real rate
-- statement:
--   **Every rate achievable by a real stationary pair is achievable by an integral one.**
--
--   Let $a, b$ be strictly positive real ten-class profiles with $b \in \mathcal N$ and $a - b \in Y$, the two-dimensional kernel of the marginal map spanned by the displayed vectors $\sigma$ and $\tau$.  Then for every
--
--   $$V \;<\; G(\tau,a)\,\frac{E(b)}{E(a)}$$
--
--   there are strictly positive **integral** profiles $\beta, \beta^{*}$ with the same nine-grade marginals, $Q\beta^{*} = Q\beta$, whose normalised partner is again stationary, $\beta^{*}/D \in \mathcal N$, and which already beat $V$:
--
--   $$V \;<\; G\bigl(\tau, \beta/D\bigr)\,\frac{E(\beta^{*}/D)}{E(\beta/D)} .$$
--
--   The point is that $\mathcal N$ is cut out by two *binomial* relations, $b_2 b_7^{2} = b_4 b_5 b_9$ and $b_3 b_7 b_8 = b_4 b_6 b_9$, both homogeneous of degree three.  Binomial equations are solvable for one variable in terms of the others, so the positive rational points of $\mathcal N$ are dense in its positive real points — one approximates eight coordinates freely and *defines* the remaining two by the relations, which then hold exactly rather than approximately.  Homogeneity means no normalisation is needed to stay on $\mathcal N$.  Together with the fact that $Y$ is spanned by two integer vectors, both profiles can be produced directly as integers on a common marginal fibre.
--
--   This is what turns the integral form of Theorem 5.3 into the real one: the rate is continuous in the profile on the positive orthant, so a strict inequality at the real pair survives the approximation.
--
--   *Formalization note.* The construction is explicit.  At scale $n$ one takes ceilings $u_i = \lceil n b_i \rceil$ of eight coordinates, multiplies through by $u_7^{2} u_8$ to clear denominators, and sets the second and third coordinates to $u_4u_5u_9u_8$ and $u_4u_6u_9u_7$; the two relations then hold as identities in $\mathbb N$.  The companion profile is obtained by adding integer multiples of the two kernel vectors, which changes neither the marginals nor the class-weighted total.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Theorem 5.3, Section 5 (Equation (5.2), its kernel, and the set N) and Section 3, Equations (3.2)-(3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_theorem53_rational_dense_rate
    (tau : ℝ) (a b : Fin 10 → ℝ)
    (hb : MME.StothersFourth.InN b)
    (haPos : ∀ i, 0 < a i) (hbPos : ∀ i, 0 < b i)
    (hsame : MME.StothersFourth.InY (fun i ↦ a i - b i))
    (V : ℝ)
    (hVlt : V < MME.StothersFourth.globalRate 6 tau a a *
      (MME.StothersFourth.entropyProduct b / MME.StothersFourth.entropyProduct a)) :
    ∃ base bstar : Fin 10 → ℕ,
      (∀ r, 0 < base r) ∧ (∀ r, 0 < bstar r) ∧
      (∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
            MME.StothersFourth.genMarginalBaseCount base j) ∧
      MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar) ∧
      V < MME.StothersFourth.globalRate 6 tau
            (MME.StothersFourth.genProfileB base)
            (MME.StothersFourth.genProfileB base) *
          (MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB bstar) /
            MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB base)) := by
  sorry
