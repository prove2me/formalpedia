-- Prove2me | Theorems.Thm_ZetaNine_quadrature_exact_of_moments
-- name    : ZetaNine.quadrature_exact_of_moments
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T02:42:30.700836+00:00
-- url     : https://prove2.me/theorems/443fb397-e2df-48a0-941c-0617ca84f5f1
-- title:
--   Exact quadrature on quartics from the first five moments
-- statement:
--   ## Exact quadrature on quartics from the first five moments
--
--   Let $L:\mathbb{R}[X]\to\mathbb{R}$ be a linear functional (the "true" weighted sum,
--   viewed as a functional on the polynomial tested against the kernel), let
--   $y,w:\{0,1,2,3,4\}\to\mathbb{R}$ be five nodes and five weights, and suppose that $L$
--   and the five-node rule $p\mapsto\sum_j w_j\,p(y_j)$ have the same moments up to degree
--   four:
--
--   $$L\bigl(X^{\,m}\bigr)=\sum_{j} w_j\,y_j^{\,m}\qquad (0\le m\le 4).$$
--
--   Then for every polynomial $p$ of degree at most four,
--
--   $$L(p)=\sum_{j=0}^{4} w_j\,p(y_j).$$
--
--   **Why.** Both sides are $\mathbb{R}$-linear in $p$. By hypothesis the two agree on the
--   five monomials $1,X,X^2,X^3,X^4$; and every polynomial of degree $\le 4$ is a linear
--   combination of them (its expansion is
--   $p=\sum_{i<5}\bigl[\text{coeff}_i\,p\bigr]\,X^{i}$). Two linear functionals agreeing on
--   a spanning set agree everywhere.
--
--   **Scope.** This is the exact algebraic core of local node **FQ** ("exact positive
--   five-sample cubature"). In the actual construction $L$ is the complete infinite
--   positive-kernel sum $\sum_{k>n}R_n(k)\,(\cdot)\bigl(k(k+n)/n^2\bigr)$ restricted to
--   quartics, the nodes are the five prescribed integers
--   $k_{n,j}=\lfloor nx_*+j\sqrt{n/a}+1/2\rfloor$, and the weights $\omega_{n,j}$ are defined
--   by solving the Vandermonde system for these five moments; the coordinate
--   $s_{n,k}$ and hence $y=k(k+n)/n^2$ is affine in it, which is what makes the quartic a
--   quartic. The statement here is the general moment-matching step, so it covers any such
--   rule. The theorem does **not** assert that the actual weights are strictly positive
--   (that is the analytic Gaussian-moment input $\omega_{n,j}\to(1/12,1/6,1/2,1/6,1/12)$),
--   and it does not assert that the actual moving first output takes one weak sign at the
--   five nodes; both remain part of the open node T5.
-- source:
--   Local zeta9 research note, roadmap/research/moving-short-sign-next.md, section 6 exact five-sample cubature, 2026-09-25

import Mathlib

namespace ZetaNine

theorem quadrature_exact_of_moments
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m) :
    ∀ p : Polynomial ℝ, p.natDegree ≤ 4 →
      L p = ∑ j : Fin 5, w j * p.eval (y j) := by sorry

end ZetaNine
