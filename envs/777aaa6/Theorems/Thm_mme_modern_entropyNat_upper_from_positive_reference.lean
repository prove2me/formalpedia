-- Prove2me | Theorems.Thm_mme_modern_entropyNat_upper_from_positive_reference
-- name    : mme_modern_entropyNat_upper_from_positive_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T03:45:31.377881+00:00
-- url     : https://prove2.me/theorems/ae0df7ed-d414-4940-996c-8707d2ab69b7
-- title:
--   Maximum-entropy upper certificate without exact reference marginals
-- statement:
--   Let $D$ be a finite set with three coordinate maps, and let $\rho$ and $y$ be probability distributions on $D$, with $y$ strictly positive. Let $\alpha$ be reference weights of total mass one whose three marginals equal those of $\rho$. For an additive potential $g(a)=\lambda_0+\lambda_X(a_X)+\lambda_Y(a_Y)+\lambda_Z(a_Z)$ and a real error allowance $\varepsilon$, suppose $g(a)-\varepsilon\le\log y(a)$ for every $a$. Then the natural-logarithm entropy obeys
--
--   $$H(\rho)\le-\sum_{a\in D}\alpha(a)g(a)+\varepsilon.$$
--
--   The positive distribution $y$ need not share the marginals of $\alpha$ or $\rho$, and no exact optimality or stationarity equations are required. This gives a finite certificate interface for bounding the maximum-entropy penalty over all distributions with prescribed marginals. The logarithmic lower bounds themselves remain explicit hypotheses.
-- source:
--   Finite Gibbs-inequality/additive-potential certificate derived for the maximum-entropy penalties in More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Propositions 5.1 and 6.3, https://arxiv.org/abs/2404.16349v2. Related to the additive-potential certificate in Dupont et al., Improving the Matrix Multiplication Exponent with Modern Optimization and AlphaEvolve, arXiv:2608.16884v1, Lemma 1, https://arxiv.org/abs/2608.16884v1; unlike the existing same-marginal reference formulation, this adapter does not require the positive reference distribution to have the target marginals. It is a new finite certificate lemma, not a separately numbered source theorem.

import Definitions.Def_mme_modern_entropy_data

open BigOperators

universe u v w x

set_option autoImplicit false

theorem mme_modern_entropyNat_upper_from_positive_reference
    {D : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    [Fintype D] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : D → X) (coordY : D → Y) (coordZ : D → Z)
    (rho alpha y : D → ℝ) (lambdaZero : ℝ)
    (lambdaX : X → ℝ) (lambdaY : Y → ℝ) (lambdaZ : Z → ℝ)
    (epsilon : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hy : ∀ a, 0 < y a)
    (hrhoSum : ∑ a, rho a = 1) (halphaSum : ∑ a, alpha a = 1)
    (hySum : ∑ a, y a = 1)
    (hmargX : ∀ i, mme_modern_marginal coordX rho i =
      mme_modern_marginal coordX alpha i)
    (hmargY : ∀ i, mme_modern_marginal coordY rho i =
      mme_modern_marginal coordY alpha i)
    (hmargZ : ∀ i, mme_modern_marginal coordZ rho i =
      mme_modern_marginal coordZ alpha i)
    (hlogLower : ∀ a,
      lambdaZero + lambdaX (coordX a) + lambdaY (coordY a) +
        lambdaZ (coordZ a) - epsilon ≤ Real.log (y a)) :
    (∑ a, Real.negMulLog (rho a)) ≤
      -(∑ a, alpha a * (lambdaZero + lambdaX (coordX a) +
        lambdaY (coordY a) + lambdaZ (coordZ a))) + epsilon := by
  sorry
