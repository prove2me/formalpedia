-- Prove2me | Theorems.Thm_YeIPA_QPApprox_qp_min_sphere_rounding
-- name    : YeIPA.QPApprox.qp_min_sphere_rounding
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:45.154812+00:00
-- url     : https://prove2.me/theorems/8859a35e-8277-4024-999b-1010733ad539
-- title:
--   Lemma 9.30 — $\underline q(Q)$ is the minimum over $V$ of $\mathbb E_u\,\sigma(V^Tu)^TDQD\sigma(V^Tu)$
-- statement:
--   Let $Q$ be a symmetric $n\times n$ matrix, $A\in\mathbb R^{m\times n}$, $A_i=\operatorname{diag}(a_i)$, $b\in\mathbb R^m$, and assume the QP $\underline q(Q)=\min\{x^TQx:\ \sum_ja_{ij}x_j^2=b_i,\ -e\le x\le e\}$ is feasible. Let $u$ be uniformly distributed on the unit sphere of $\mathbb R^n$, let $\sigma(w)$ be the vector of signs $\operatorname{sign}(w_j)$ with $\operatorname{sign}(t)=1$ for $t\ge0$ and $-1$ otherwise, and for $V\in\mathbb R^{n\times n}$ with columns $v_1,\dots,v_n$ let $D=\operatorname{diag}(\|v_1\|,\dots,\|v_n\|)$. Then
--   $$\underline q(Q)=\min\ \mathbb E_u\big(\sigma(V^Tu)^TDQD\,\sigma(V^Tu)\big)\quad\text{s.t.}\quad A_i\bullet(V^TV)=b_i\ (i=1,\dots,m),\quad \|v_j\|\le1\ (j=1,\dots,n):$$
--   for every $V$ satisfying the constraints the expectation is at least $\underline q(Q)$, and some such $V$ attains $\underline q(Q)$.
--
--   The lemma rewrites the nonconvex QP as an optimization over Gram factors $V$ of the relaxation's matrices, with the sign rounding as objective; Theorem 9.32 evaluates the expectation in closed form.
--
--   **Formalization Note** The standing assumptions of §9.5 (p. 325), $Q$ symmetric and the QP feasible, are hypotheses. "Minimize" is stated as a lower bound that is attained. The expectation is the integral against the normalized surface measure on the unit sphere of `EuclideanSpace ℝ (Fin n)`; the integrand is bounded and measurable, so it is integrable. $V$ is an $n\times n$ matrix, as $\underline V$ on p. 326.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 327, Lemma 9.30

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation

open Matrix MeasureTheory

namespace YeIPA.QPApprox

variable {m n : ℕ}

/-- **Lemma 9.30** (Ye, *Interior Point Algorithms*, Wiley 1997, p. 327).

Let `u` be uniformly distributed on the unit sphere in `ℝⁿ`. Then
`q̲(Q) = minimize E_u(σ(Vᵀu)ᵀ DQD σ(Vᵀu))` s.t. `A_i • (VᵀV) = b_i` (`i = 1, …, m`),
`‖v_j‖ ≤ 1` (`j = 1, …, n`), where `D = diag(‖v_1‖, …, ‖v_n‖)` and `v_j` is the `j`-th column
of `V ∈ ℝ^{n×n}`. "Minimize" is stated as: `q̲(Q)` is a lower bound of the objective at every
feasible `V`, and is attained at some feasible `V`.

Standing assumptions of §9.5 (p. 325): `Q` symmetric, the QP feasible. -/
theorem qp_min_sphere_rounding (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x) :
    (∀ V : Matrix (Fin n) (Fin n) ℝ,
      (∀ i, frob (constrMat A i) (Vᵀ * V) = b i) → (∀ j, colNorm V j ≤ 1) →
      qpMin Q A b ≤ ∫ u, sigma (Vᵀ *ᵥ coords u) ⬝ᵥ
        ((colNormDiag V * Q * colNormDiag V) *ᵥ sigma (Vᵀ *ᵥ coords u)) ∂(sphereUniform n)) ∧
    ∃ V : Matrix (Fin n) (Fin n) ℝ,
      (∀ i, frob (constrMat A i) (Vᵀ * V) = b i) ∧ (∀ j, colNorm V j ≤ 1) ∧
      (∫ u, sigma (Vᵀ *ᵥ coords u) ⬝ᵥ
        ((colNormDiag V * Q * colNormDiag V) *ᵥ sigma (Vᵀ *ᵥ coords u)) ∂(sphereUniform n))
        = qpMin Q A b := by sorry

end YeIPA.QPApprox
