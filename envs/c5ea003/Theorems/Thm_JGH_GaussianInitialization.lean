-- Prove2me | Theorems.Thm_JGH_GaussianInitialization
-- name    : JGH.GaussianInitialization
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T01:33:10.895052+00:00
-- url     : https://prove2.me/theorems/50234d24-c239-418f-ae16-3538ec6b69e0
-- title:
--   Proposition 1 — Gaussian Process Limit at Initialization
-- statement:
--   ### Mathematical statement
--   For all positive input and output dimensions, arbitrary
--   hidden-layer count $h$, positive bias scale, and Lipschitz activation, the initialized
--   output vector on every fixed finite input family converges in distribution:
--   $$\big(f_{\theta,k}(x_i)\big)_{i<N,k<q}
--   \ \Longrightarrow\ \mathcal N\!\left(0,
--   [\Sigma^{(h+1)}(x_i,x_j)\delta_{kk'}]_{(i,k),(j,k')}\right).$$
--   Widths tend to infinity in the sequential order defined below. The Gaussian
--   outputs are independent across output coordinates, but generally correlated
--   across inputs. Formalization note: direct source Proposition 1 in its full
--   finite-dimensional-distribution formulation, rather than a claim about a topology
--   on all functions on the input space.
--
--   Source: Arthur Jacot, Franck Gabriel, Clément Hongler, Neural Tangent Kernel: Convergence and Generalization in Neural Networks, NeurIPS 2018, arXiv:1806.07572v4, https://arxiv.org/abs/1806.07572v4; Section 4.1, PDF p. 5, Proposition 1; Appendix A.1, PDF p. 11 and PDF p. 12, Proposition 1 and its proof. Displays are unnumbered.
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
--   Arthur Jacot, Franck Gabriel, Clément Hongler, Neural Tangent Kernel: Convergence and Generalization in Neural Networks, NeurIPS 2018, arXiv:1806.07572v4, https://arxiv.org/abs/1806.07572v4; Section 4.1, PDF p. 5, Proposition 1; Appendix A.1, PDF p. 11 and PDF p. 12, Proposition 1 and its proof. Displays are unnumbered.

import Definitions.Def_JGH_NTK_Model
open MeasureTheory Filter
open scoped Topology NNReal

namespace JGH
theorem GaussianInitialization :
  ∀ (d q : ℕ), 0 < d → 0 < q →
    ∀ (σ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K σ →
      ∀ (β : ℝ), 0 < β → ∀ (h N : ℕ) (X : Fin N → Input d),
        TendstoInDistribution (initializedOutput (h := h) d q σ β X)
          (sequentialWidths h) id (fun w ↦ initialization (h + 1) (widths d q w))
          (outputGaussian d q σ β h X) := by sorry
end JGH
