-- Prove2me | Theorems.Thm_FedRemoval_ExactNewtonRemoval
-- name    : FedRemoval.ExactNewtonRemoval
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-28T21:48:27.75621+00:00
-- url     : https://prove2.me/theorems/86e63a71-6665-465f-8164-5a51f1c05557
-- title:
--   Equation (1) — Exact Newton Removal for the Retained Quadratic
-- statement:
--   For every nonempty retained set $S$, $\mu>0$, and every
--   starting parameter $w$, prove
--   $$w-H_S^{-1}g_S(w)=u_S.$$
--   Formalization note: source-derived equation (1), expressed for an arbitrary
--   starting point of a positive-definite quadratic. It reaches the retained
--   optimum; it does not assert equality with an unfinished retraining run.
--
--   Source: Ruinan Jin, Minghui Chen, Qiong Zhang, Xiaoxiao Li, Forgettable Federated Linear Learning with Certified Data Unlearning, IEEE TNNLS (2026), arXiv:2306.02216v3, https://arxiv.org/pdf/2306.02216v3; Section II-B (Section 2), PDF p. 3, equation (1).
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
--   Ruinan Jin, Minghui Chen, Qiong Zhang, Xiaoxiao Li, Forgettable Federated Linear Learning with Certified Data Unlearning, IEEE TNNLS (2026), arXiv:2306.02216v3, https://arxiv.org/pdf/2306.02216v3; Section II-B (Section 2), PDF p. 3, equation (1).

import Definitions.Def_FedRemoval_Model

namespace FedRemoval
theorem ExactNewtonRemoval :
∀ (n d k : ℕ) (D : Data n d k) (s : Finset (Fin n)) (μ : ℝ),
    s.Nonempty → 0 < μ →
    ∀ w, w - exactCorrection D s μ w = optimum D s μ := by sorry
end FedRemoval
