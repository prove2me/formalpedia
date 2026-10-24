-- Prove2me | Theorems.Thm_YeIPA_QPApprox_qp_min_arcsin_infimum
-- name    : YeIPA.QPApprox.qp_min_arcsin_infimum
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:38.84873+00:00
-- url     : https://prove2.me/theorems/7fd5f733-12ab-4d83-964a-3922d9f66f54
-- title:
--   Theorem 9.32 — $\underline q(Q)$ is the infimum of $\frac2\pi Q\bullet(D\arcsin[D^{-1}XD^{-1}]D)$ over feasible $X\succ0$
-- statement:
--   Let $Q$ be a symmetric $n\times n$ matrix, $A\in\mathbb R^{m\times n}$, $A_i=\operatorname{diag}(a_i)$, $b\in\mathbb R^m$, and assume the QP $\underline q(Q)=\min\{x^TQx:\ \sum_ja_{ij}x_j^2=b_i,\ -e\le x\le e\}$ is feasible. For a positive definite $X$ let $D=\operatorname{diag}(\sqrt{x_{11}},\dots,\sqrt{x_{nn}})$ and let $\arcsin[\cdot]$ act entrywise. Then
--   $$\underline q(Q)=\inf\Big\{\tfrac2\pi\,Q\bullet\big(D\arcsin[D^{-1}XD^{-1}]D\big):\ A_i\bullet X=b_i\ (i=1,\dots,m),\ d(X)\le e,\ X\succ0\Big\}.$$
--
--   The theorem evaluates the expected value of the sign rounding of Lemma 9.30 in closed form and is the main input to Theorem 9.33.
--
--   **Formalization Note** The standing assumptions of §9.5 (p. 325), $Q$ symmetric and the QP feasible, are hypotheses; no positive definite feasible $X$ is assumed, as on the page. "Infimum" is stated as `IsGLB`: $\underline q(Q)$ is the greatest lower bound of the set of values, so the statement is false when that set is empty. Finding F1 shows that this happens for a feasible QP whose constraints force some $x_j=0$; the item `qp_min_arcsin_infimum_corrected` adds the missing hypothesis. $D^{-1}$ is Mathlib's matrix inverse, the true inverse here since $x_{jj}>0$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 328, Theorem 9.32

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation

open Matrix MeasureTheory

namespace YeIPA.QPApprox

variable {m n : ℕ}

/-- **Theorem 9.32** (Ye, *Interior Point Algorithms*, Wiley 1997, p. 328), as printed.

`q̲(Q) = infimum (2/π) Q • (D arcsin[D⁻¹XD⁻¹]D)` s.t. `A_i • X = b_i` (`i = 1, …, m`),
`d(X) ≤ e`, `X ≻ 0`, where `D = diag(√x_11, …, √x_nn)`. "Infimum" is `IsGLB`: `q̲(Q)` is the
greatest lower bound of the set of these values (so the statement fails if the set is empty).

Standing assumptions of §9.5 (p. 325): `Q` symmetric, the QP feasible. No positive definite
feasible `X` is assumed (see FINDINGS.yaml F1 and the corrected variant). -/
theorem qp_min_arcsin_infimum (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x) :
    IsGLB {t : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
        (∀ i, frob (constrMat A i) X = b i) ∧ (∀ j, diagVec X j ≤ 1) ∧ X.PosDef ∧
        t = (2 / Real.pi) * frob Q (arcsinTransform X)}
      (qpMin Q A b) := by sorry

end YeIPA.QPApprox
