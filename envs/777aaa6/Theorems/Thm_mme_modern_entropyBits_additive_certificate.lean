-- Prove2me | Theorems.Thm_mme_modern_entropyBits_additive_certificate
-- name    : mme_modern_entropyBits_additive_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:34:50.78072+00:00
-- url     : https://prove2.me/theorems/0fb23ec9-5212-4428-9810-3f8f759886d5
-- title:
--   Additive-potential certificate for constrained maximum entropy
-- statement:
--   Let $D$ be a finite set of shapes with three coordinate maps $a\mapsto a_X$, $a\mapsto a_Y$, and $a\mapsto a_Z$. Let $\rho$ and $y$ be probability distributions on $D$, with $y(a)>0$ for every shape, and assume that they have the same $X$-, $Y$-, and $Z$-marginals.
--
--   Let $\varepsilon\ge0$. Suppose there are a constant $\lambda_0$ and marginal potentials $\lambda_X,\lambda_Y,\lambda_Z$ such that, for every $a\in D$,
--
--   $$
--   \left|\log_2 y(a)-\bigl(\lambda_0+\lambda_X(a_X)+\lambda_Y(a_Y)+\lambda_Z(a_Z)\bigr)\right|\le\varepsilon.
--   $$
--
--   Then the base-two Shannon entropies satisfy
--
--   $$
--   H_2(\rho)\le H_2(y)+2\varepsilon.
--   $$
--
--   Because $\rho$ is arbitrary among distributions with the prescribed marginals, this is the pointwise form of the upper bound $H_D^{\max}\le H_2(y)+2\varepsilon$ in Lemma 1. It turns an approximate additive-potential witness into a compact, independently checkable upper certificate and is reusable at every maximum-entropy node of a More Asymmetry optimization tree.
--
--   **Formalization Note** Probability distributions are represented as real-valued functions with explicit nonnegativity and normalization hypotheses. Strict positivity is required only for the certified distribution $y$, exactly as in the source.
-- source:
--   E. Dupont et al., Improving the matrix multiplication exponent with modern optimization and AlphaEvolve, arXiv:2608.16884, Section 2.5, Equation (12), Lemma 1 and its proof, printed pp. 8–9; https://arxiv.org/abs/2608.16884

import Definitions.Def_mme_modern_entropy_data

open BigOperators

universe u v w x

theorem mme_modern_entropyBits_additive_certificate
    {D : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    [Fintype D] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : D → X) (coordY : D → Y) (coordZ : D → Z)
    (rho y : D → ℝ)
    (lambdaZero : ℝ)
    (lambdaX : X → ℝ) (lambdaY : Y → ℝ) (lambdaZ : Z → ℝ)
    (ε : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hy : ∀ a, 0 < y a)
    (hrhoSum : ∑ a, rho a = 1) (hySum : ∑ a, y a = 1)
    (hmargX : ∀ i, mme_modern_marginal coordX rho i =
      mme_modern_marginal coordX y i)
    (hmargY : ∀ i, mme_modern_marginal coordY rho i =
      mme_modern_marginal coordY y i)
    (hmargZ : ∀ i, mme_modern_marginal coordZ rho i =
      mme_modern_marginal coordZ y i)
    (hε : 0 ≤ ε)
    (hcertificate : ∀ a,
      |Real.log (y a) / Real.log 2 -
        (lambdaZero + lambdaX (coordX a) + lambdaY (coordY a) +
          lambdaZ (coordZ a))| ≤ ε) :
    mme_modern_entropyBits rho ≤ mme_modern_entropyBits y + 2 * ε := by sorry
