-- Prove2me | Theorems.Thm_SCAFFOLD_PerturbedStrongConvexity
-- name    : SCAFFOLD.PerturbedStrongConvexity
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-23T05:36:32.321252+00:00
-- url     : https://prove2.me/theorems/f5e300cc-b8c1-403d-bf13-8852f2a7dd75
-- title:
--   Lemma 5 — Perturbed strong convexity
-- statement:
--   If the clients are $\mu$-strongly convex with $\mu\ge0$, then
--   for every client $i$ and every $x,y,z\in\mathbb R^d$,
--   $$\langle\nabla f_i(x),z-y\rangle\ge
--   f_i(z)-f_i(y)+\frac\mu4\|y-z\|^2-\beta\|z-x\|^2.$$
--   Formalization note: direct source Lemma 5 applied to each client loss, including
--   its convex ($\mu=0$) boundary. No stochastic run or minimizer is required.
--
--   Source: Sai Praneeth Karimireddy, Satyen Kale, Mehryar Mohri, Sashank J. Reddi, Sebastian U. Stich, and Ananda Theertha Suresh, SCAFFOLD: Stochastic Controlled Averaging for Federated Learning, ICML 2020; arXiv:1910.06378v4, https://arxiv.org/abs/1910.06378v4; Appendix C, PDF p. 17, Lemma 5 (unnumbered display), used in Section 5.
--
--   ### Notation and probability model
--   There are $N\ge1$ clients, a model space $\mathbb R^d$ (including $d=0$),
--   differentiable client losses $f_i$ with $\beta$-Lipschitz gradients, $\beta>0$,
--   and $f=N^{-1}\sum_i f_i$. The starting point $x^0$ is deterministic and
--   $\sigma\ge0$ bounds within-client stochastic-gradient standard deviation.
--   A run has $T\ge1$ rounds, $K\ge1$ local steps, $1\le S\le N$ clients per round,
--   local step $\eta_l>0$, global step $\eta_g\ge1$, and $h=K\eta_l\eta_g$.
--   All random variables live on a standard Borel probability space $(\Omega,\mathcal A,\nu)$ with a filtration
--   containing the full history. States and gradient samples are square integrable;
--   gradient samples are conditionally unbiased, have conditional squared error at
--   most $\sigma^2$, and are independent across clients conditional on each step's
--   history. These are explicit fresh-oracle and finite-moment conventions.
--
--   Every round first defines virtual paths for all clients, starting at $y_{i,0}^r=x^r$:
--   $$y_{i,k+1}^r=y_{i,k}^r-\eta_l(g_{i,k}^r-c_i^r+c^r),\qquad
--   c^r=N^{-1}\sum_i c_i^r.$$
--   Then an $S$-element subset is sampled uniformly, conditionally independently of
--   these paths given the past. Equivalently, its conditional distribution given the
--   entire completed virtual-path history is uniform. Only selected clients update
--   their controls to $K^{-1}\sum_{k=0}^{K-1}g_{i,k}^r$; other controls persist.
--   The server update is $x^{r+1}=x^r+(\eta_g/S)\sum_{i\in\mathcal S_r}(y_{i,K}^r-x^r)$.
--   This is option II of Algorithm 1, with the average-gradient form of Appendix E.
--   The model contains the algorithm and oracle laws, not any convergence inequality.
--
--   For convex targets, $x^\star$ minimizes $f$, and the client losses obey
--   $$f_i(y)\ge f_i(x)+\langle\nabla f_i(x),y-x\rangle
--   +\frac\mu2\|y-x\|^2,\qquad \mu\ge0.$$
--   The initial client controls $c_i^0$ are arbitrary deterministic vectors and
--   the server control is their average. Define
--   $$C_0=\frac1N\sum_i\|c_i^0-\nabla f_i(x^\star)\|^2,\qquad
--   V_0=\|x^0-x^\star\|^2+\frac{9Nh^2}{S}C_0.$$
--   For nonconvex targets, $f_{\rm low}\le f(x)$ for all $x$; a minimizer need not
--   exist. Each $c_i^0$ is instead initialized by averaging $K$ fresh stochastic
--   gradients at $x^0$, with the same conditional oracle assumptions. These full-client
--   initialization queries are additional to the $T$ optimization rounds.
--
--   The output is a sampled pre-round server iterate among $x^0,\ldots,x^{T-1}$,
--   represented by its expected loss or squared-gradient statistic. No last-iterate
--   or pathwise guarantee is asserted. Sources: Section 2, PDF p. 2; Algorithm 1,
--   PDF p. 4; Appendix B.1, PDF p. 14, assumptions A3–A5; Appendix E, PDF pp. 25–26,
--   equations (18)–(22), Remark 10; Appendix E.2, PDF pp. 31 and 35, equations
--   (26)–(27) and final warm-start paragraph.
--   Primary reference: Karimireddy et al., *SCAFFOLD: Stochastic Controlled Averaging
--   for Federated Learning*, ICML 2020, https://arxiv.org/abs/1910.06378v4.
-- source:
--   Sai Praneeth Karimireddy, Satyen Kale, Mehryar Mohri, Sashank J. Reddi, Sebastian U. Stich, and Ananda Theertha Suresh, SCAFFOLD: Stochastic Controlled Averaging for Federated Learning, ICML 2020; arXiv:1910.06378v4, https://arxiv.org/abs/1910.06378v4; Appendix C, PDF p. 17, Lemma 5 (unnumbered display), used in Section 5.

import Definitions.Def_SCAFFOLD_Model
open MeasureTheory
universe u

namespace SCAFFOLD
theorem PerturbedStrongConvexity :
  ∀ (d N : ℕ) (P : Problem d N) (μ : ℝ), Convexity P μ →
    ∀ (i : Fin N) (x y z : Space d),
      P.f i z - P.f i y + μ / 4 * ‖y - z‖ ^ 2 - P.β * ‖z - x‖ ^ 2 ≤
        inner ℝ (gradient (P.f i) x) (z - y) := by sorry
end SCAFFOLD
