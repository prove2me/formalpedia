-- Prove2me | Theorems.Thm_FedRemoval_InversePerturbation
-- name    : FedRemoval.InversePerturbation
-- status  : Open
-- author  : @Minghui
-- created : 2026-09-28T21:50:56.900333+00:00
-- url     : https://prove2.me/theorems/44785ef9-8f92-44cf-b965-8a3654c1acc3
-- title:
--   Section C5 — Corrected Inverse-Hessian Perturbation
-- statement:
--   For nonempty retained and server datasets and $\mu>0$, prove
--   $$H_P^{-1}-H_S^{-1}=H_P^{-1}(G_S-G_P)H_S^{-1},$$
--   $$\|H_P^{-1}-H_S^{-1}\|\le
--   \|H_P^{-1}\|\|G_S-G_P\|\|H_S^{-1}\|.$$
--   Formalization note: explicitly corrected replacement for the general inverse
--   estimate in supplementary Section C5. Both inverse factors are retained;
--   this is not the incorrect single-inverse-factor formula printed there.
--
--   Source: Ruinan Jin, Minghui Chen, Qiong Zhang, Xiaoxiao Li, Forgettable Federated Linear Learning with Certified Data Unlearning, IEEE TNNLS (2026), arXiv:2306.02216v3, https://arxiv.org/pdf/2306.02216v3; Section III-C (Section 3), PDF p. 5 and PDF p. 6, Theorem 2; supplementary Section C5, PDF p. 16, unnumbered error-decomposition and inverse-perturbation displays.
--
--   ### Notation and hypotheses
--   The full dataset has $n$ records and the server dataset has $q$ records.
--   Record $i$ has a fixed real linear feature map $A_i:\mathbb R^d\to\mathbb R^k$,
--   offset $a_i\in\mathbb R^k$, and target $y_i\in\mathbb R^k$.
--   For a retained subset $S$ and regularization $\mu$, define
--   $$L_S(w)=\frac1{2|S|}\sum_{i\in S}\|A_iw+a_i-y_i\|^2+
--   \frac\mu2\|w\|^2,\quad
--   G_S=\frac1{|S|}\sum_{i\in S}A_i^*A_i,\quad H_S=G_S+\mu I,$$
--   $$b_S=\frac1{|S|}\sum_{i\in S}A_i^*(y_i-a_i),\quad
--   u_S=H_S^{-1}b_S,\quad g_S(w)=H_Sw-b_S.$$
--   Here $u_D$ uses all full-data indices, and $H_P,G_P$ use all server indices.
--   Only the server feature maps enter its removal surrogate; server targets and offsets are unused.
--   All norms are Euclidean vector or induced operator norms, as appropriate.
--   The inverse is the total ring inverse; theorems must derive its validity from
--   $\mu>0$, not assume it. Empty empirical averages are defined by Lean's total
--   arithmetic, but the relevant theorems require $S\ne\varnothing$ and, when
--   server data appear, $q>0$. Zero parameter or output dimension is allowed.
--
--   Set
--   $$F_w(v)=\tfrac12\langle v,H_Pv\rangle-\langle g_S(w),v\rangle,
--   \quad v_P(w)=H_P^{-1}g_S(w),\quad
--   \operatorname{gap}(w,v)=F_w(v)-F_w(v_P(w)),
--   \quad\kappa=\|H_P^{-1}\|\|G_P-G_S\|.$$
--
--   The probability model used only by the final target is a finite joint law
--   on $\Omega=\{0,\ldots,N-1\}$: masses $p_\omega\ge0$ sum to one and
--   $\mathbb E[f]=\sum_{\omega\in\Omega}p_\omega f(\omega)$.
--   It allows arbitrary dependence between outputs. No law exists for $N=0$.
--   The other targets are deterministic and assume no probability model.
--
--   Formalization note: the fixed affine-feature model is source-derived from
--   Jin et al., arXiv:2306.02216v3, Section III-A (Section 3), PDF p. 3,
--   equation (3), and PDF p. 4, equations (4)--(5). Arbitrary real targets and
--   nonempty retained subsets explicitly extend the one-hot/client-removal
--   setting. The finite-law error targets are corrected formulations, not
--   transcriptions or proofs of the printed Theorem 2.
-- source:
--   Ruinan Jin, Minghui Chen, Qiong Zhang, Xiaoxiao Li, Forgettable Federated Linear Learning with Certified Data Unlearning, IEEE TNNLS (2026), arXiv:2306.02216v3, https://arxiv.org/pdf/2306.02216v3; Section III-C (Section 3), PDF p. 5 and PDF p. 6, Theorem 2; supplementary Section C5, PDF p. 16, unnumbered error-decomposition and inverse-perturbation displays.

import Definitions.Def_FedRemoval_Model

namespace FedRemoval
theorem InversePerturbation :
∀ (n q d k : ℕ) (D : Data n d k) (s : Finset (Fin n)) (P : Data q d k) (μ : ℝ),
    s.Nonempty → 0 < q → 0 < μ →
    inverseHessian P Finset.univ μ - inverseHessian D s μ =
      (inverseHessian P Finset.univ μ).comp
        ((gram D s - gram P Finset.univ).comp (inverseHessian D s μ)) ∧
    ‖inverseHessian P Finset.univ μ - inverseHessian D s μ‖ ≤
      ‖inverseHessian P Finset.univ μ‖ * ‖gram D s - gram P Finset.univ‖ *
        ‖inverseHessian D s μ‖ := by sorry
end FedRemoval
