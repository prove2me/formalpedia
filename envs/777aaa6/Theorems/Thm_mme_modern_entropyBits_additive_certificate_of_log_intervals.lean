-- Prove2me | Theorems.Thm_mme_modern_entropyBits_additive_certificate_of_log_intervals
-- name    : mme_modern_entropyBits_additive_certificate_of_log_intervals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T15:10:32.277375+00:00
-- url     : https://prove2.me/theorems/c0225981-3fd2-464b-af9b-f5461decc897
-- title:
--   Directed log intervals certify the modern maximum-entropy bound
-- statement:
--   Let $\rho$ and $y$ be probability distributions on a finite set $D$ with three coordinate maps. Assume $y$ is strictly positive and the distributions have the same marginal in each coordinate. Fix $\varepsilon\ge0$ and an additive potential $g(a)=\lambda_0+\lambda_X(a_X)+\lambda_Y(a_Y)+\lambda_Z(a_Z)$. Suppose real lower and upper bounds satisfy, for every $a\in D$,
--
--   $$g(a)-\varepsilon\le L(a)\le\log_2 y(a)\le U(a)\le g(a)+\varepsilon.$$
--
--   Then the base-two Shannon entropies satisfy
--
--   $$H_2(\rho)\le H_2(y)+2\varepsilon.$$
--
--   This is the interval-input form of the additive-potential maximum-entropy certificate. It isolates the interface between independently certified logarithm bounds and the real entropy argument. The bounds may in particular come from rational interval certificates; the theorem itself assumes their validity and does not compute them.
-- source:
--   E. Dupont et al., Improving the Matrix Multiplication Exponent with Modern Optimization and AlphaEvolve, arXiv:2608.16884v1, Sections 2.5 and 4, Lemma 1 and rigorous rational verification of directed logarithm bounds; https://arxiv.org/abs/2608.16884

import Theorems.Thm_mme_modern_entropyBits_additive_certificate

open BigOperators

universe u v w x

theorem mme_modern_entropyBits_additive_certificate_of_log_intervals
    {D : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    [Fintype D] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : D → X) (coordY : D → Y) (coordZ : D → Z)
    (rho y : D → ℝ)
    (lambdaZero : ℝ)
    (lambdaX : X → ℝ) (lambdaY : Y → ℝ) (lambdaZ : Z → ℝ)
    (lower upper : D → ℝ) (ε : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hy : ∀ a, 0 < y a)
    (hrhoSum : ∑ a, rho a = 1) (hySum : ∑ a, y a = 1)
    (hmargX : ∀ i, mme_modern_marginal coordX rho i =
      mme_modern_marginal coordX y i)
    (hmargY : ∀ i, mme_modern_marginal coordY rho i =
      mme_modern_marginal coordY y i)
    (hmargZ : ∀ i, mme_modern_marginal coordZ rho i =
      mme_modern_marginal coordZ y i)
    (hε : 0 ≤ ε)
    (hlogLower : ∀ a, lower a ≤ Real.log (y a) / Real.log 2)
    (hlogUpper : ∀ a, Real.log (y a) / Real.log 2 ≤ upper a)
    (hintervalLower : ∀ a,
      lambdaZero + lambdaX (coordX a) + lambdaY (coordY a) +
          lambdaZ (coordZ a) - ε ≤ lower a)
    (hintervalUpper : ∀ a,
      upper a ≤ lambdaZero + lambdaX (coordX a) +
          lambdaY (coordY a) + lambdaZ (coordZ a) + ε) :
    mme_modern_entropyBits rho ≤ mme_modern_entropyBits y + 2 * ε := by sorry
