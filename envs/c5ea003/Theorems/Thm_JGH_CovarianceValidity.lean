-- Prove2me | Theorems.Thm_JGH_CovarianceValidity
-- name    : JGH.CovarianceValidity
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T01:32:55.803799+00:00
-- url     : https://prove2.me/theorems/b776bec8-2726-4eaf-aaf6-abcf9c3a5f5e
-- title:
--   Proposition 1 — Validity of the Recursive Gaussian Covariance
-- statement:
--   ### Mathematical statement
--   For every $d\ge1$, Lipschitz $\sigma$ with a nonnegative
--   Lipschitz constant $K$, $\beta>0$, depth $L=h+1\ge1$, and finite input family $X$,
--   $$[\Sigma^{(L)}(x_i,x_j)]_{i,j<N}\succeq0,
--   \qquad \Sigma^{(L)}(x,x)\ge\beta^2\quad\text{for every }x\in\mathbb R^d.$$
--   Formalization note: this is a paper-derived well-definedness statement for the
--   recursive covariance in Proposition 1, not a separately numbered theorem.
--   It permits singular Gram matrices and proves positive marginal variance without
--   assuming either property.
--
--   Source: Arthur Jacot, Franck Gabriel, Clément Hongler, Neural Tangent Kernel: Convergence and Generalization in Neural Networks, NeurIPS 2018, arXiv:1806.07572v4, https://arxiv.org/abs/1806.07572v4; Section 4.1, PDF p. 5, Proposition 1 and Remark 2; Appendix A.1, PDF p. 11 and PDF p. 12, Proposition 1. Displays are unnumbered.
--
--   ### Notation and probability model
--   Let $d,q\ge1$ be the input and output dimensions, $h\ge0$ the number of hidden
--   layers, $L=h+1$, $\beta>0$, and $\sigma:\mathbb R\to\mathbb R$ a Lipschitz
--   activation with a nonnegative Lipschitz constant $K$. For widths
--   $n_0=d$, $n_L=q$, and $n_\ell=w_{\ell-1}+1$ with $w_i\in\mathbb N$, the
--   probability space $\Omega_w$ is the finite real parameter space with every
--   weight and bias coordinate independently $\mathcal N(0,1)$. Its law is $\mathbb P_w$.
--   The network has the recursion
--   $$z^{(\ell+1)}_j(x)=\frac{1}{\sqrt{n_\ell}}\sum_i W^{(\ell)}_{ji}
--   a^{(\ell)}_i(x)+\beta b^{(\ell)}_j,\qquad
--    a^{(0)}(x)=x,\quad a^{(\ell)}(x)=\sigma(z^{(\ell)}(x))\ (1\le\ell\le h),$$
--   with output $f_\theta=z^{(L)}$. The full kernel, including all weights and biases, is
--   $$\Theta^{(L)}_{kk'}(\theta;x,y)=\sum_p
--   \partial_{\theta_p}f_{\theta,k}(x)\partial_{\theta_p}f_{\theta,k'}(y).$$
--   For a centered Gaussian pair $(U,V)$ with covariance induced by
--   $\Sigma^{(\ell)}$ on $(x,y)$, put
--   $$\Sigma^{(1)}(x,y)=\langle x,y\rangle/d+\beta^2,\qquad
--   \Sigma^{(\ell+1)}(x,y)=\mathbb E[\sigma(U)\sigma(V)]+\beta^2,$$
--   $$\dot\Sigma^{(\ell+1)}(x,y)=\mathbb E[\sigma'(U)\sigma'(V)],\qquad
--   \Theta_\infty^{(1)}=\Sigma^{(1)},\quad
--   \Theta_\infty^{(\ell+1)}=\Theta_\infty^{(\ell)}\dot\Sigma^{(\ell+1)}+\Sigma^{(\ell+1)}.$$
--   All kernel products in the last expression are pointwise. Local index $h$ in
--   `covarianceKernel` and `limitingNTK` denotes paper depth $h+1$.
--   The dataset $X=(x_i)_{i<N}$ is any fixed finite family; repetitions and $N=0$
--   are allowed. $\delta_{kk'}$ is the Kronecker delta.
--
--   The limit takes $n_1$ to infinity first and $n_h$ last. More precisely, for
--   any required error tolerance, the width condition is
--   $\forall^{\mathrm{eventually}}w_{h-1}\cdots
--   \forall^{\mathrm{eventually}}w_0$; each inner threshold may depend on the fixed
--   outer widths. For $h=0$ the filter is concentrated on the unique empty width
--   vector, so the statements require the exact affine base case. This is not a
--   simultaneous-width or whole-input-space uniform limit.
--
--   Formalization note: Gaussian measures are concrete Mathlib measures, including
--   singular covariance. The covariance-validity milestone establishes their
--   covariance interpretation; it is not a hypothesis of either convergence target.
--   The activation assumption is only Lipschitz. Derivatives take Mathlib's zero
--   value at points without derivatives, and proofs must justify the null exceptional
--   set under positive Gaussian bias. Native convergence in distribution includes
--   almost-everywhere measurability and weak convergence of probability laws.
--   Primary source conventions: Jacot–Gabriel–Hongler, Section 2, PDF pp. 2–3;
--   Section 4.1, PDF p. 5, Proposition 1, Theorem 1 and Remarks 2–3; Appendix A
--   opening paragraphs, PDF p. 11, and Appendix A.1, PDF pp. 11–13.
--   The relevant displays have no equation numbers.
-- source:
--   Arthur Jacot, Franck Gabriel, Clément Hongler, Neural Tangent Kernel: Convergence and Generalization in Neural Networks, NeurIPS 2018, arXiv:1806.07572v4, https://arxiv.org/abs/1806.07572v4; Section 4.1, PDF p. 5, Proposition 1 and Remark 2; Appendix A.1, PDF p. 11 and PDF p. 12, Proposition 1. Displays are unnumbered.

import Definitions.Def_JGH_NTK_Model
open MeasureTheory Filter
open scoped Topology NNReal

namespace JGH
theorem CovarianceValidity :
  ∀ (d : ℕ), 0 < d → ∀ (σ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K σ →
    ∀ (β : ℝ), 0 < β → ∀ (h N : ℕ) (X : Fin N → Input d),
      (Matrix.of (fun i j ↦ covarianceKernel d σ β h (X i) (X j))).PosSemidef ∧
        ∀ x : Input d, β ^ 2 ≤ covarianceKernel d σ β h x x := by sorry
end JGH
