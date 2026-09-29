-- Prove2me | Theorems.Thm_FedRemoval_CorrectedMeanSquareRemovalBound
-- name    : FedRemoval.CorrectedMeanSquareRemovalBound
-- status  : Open
-- author  : @Minghui
-- created : 2026-09-28T22:08:56.557339+00:00
-- url     : https://prove2.me/theorems/1a437096-42b6-49a2-8fa2-baf79a75c87b
-- title:
--   Corrected Finite-Run Mean-Square FedRemoval Bound
-- statement:
--   Let the retained and server datasets be nonempty and
--   $\mu>0$. On any finite joint probability law, let $W,V,R$ be arbitrary
--   parameter-valued output maps. The unlearned parameter is $W-V$.
--   Define $E_{\rm train}=\mathbb E\|W-u_D\|^2$,
--   $E_{\rm retrain}=\mathbb E\|R-u_S\|^2$, and
--   $Q=\mathbb E[\operatorname{gap}(W,V)]$. Prove
--   $$\mathbb E\|W-V-R\|^2\le\frac6\mu Q+
--   6\kappa^2\bigl(E_{\rm train}+\|u_D-u_S\|^2\bigr)+3E_{\rm retrain}.$$
--   This quantifies how the actual finite-run optimization errors and the
--   server/retained Hessian mismatch affect parameter error.
--
--   Formalization note: user-authorized corrected, source-derived formulation
--   motivated by Theorem 2 and Section C5. It retains the full-to-retained optimum
--   displacement, the inverse-Hessian scale, and unfinished retraining error.
--   It applies to arbitrary finite-support output laws, with no independence
--   assumption. It does not assert the printed constants/rate, does not define
--   a FedAvg or SGD run, and does not imply statistical indistinguishability or
--   differential privacy. Algorithm-specific bounds on $Q,E_{\rm train},E_{\rm retrain}$
--   remain separate work.
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
theorem CorrectedMeanSquareRemovalBound :
∀ (n q d k N : ℕ) (D : Data n d k) (s : Finset (Fin n)) (P : Data q d k)
    (μ : ℝ) (p : Law N) (w v r : Fin N → E d),
    s.Nonempty → 0 < q → 0 < μ →
    mean p (fun i ↦ ‖w i - v i - r i‖ ^ 2) ≤
      (6 / μ) * mean p (fun i ↦ solverGap D s P μ (w i) (v i)) +
      6 * mismatch D s P μ ^ 2 *
        (mse p w (optimum D Finset.univ μ) +
          ‖optimum D Finset.univ μ - optimum D s μ‖ ^ 2) +
      3 * mse p r (optimum D s μ) := by sorry
end FedRemoval
