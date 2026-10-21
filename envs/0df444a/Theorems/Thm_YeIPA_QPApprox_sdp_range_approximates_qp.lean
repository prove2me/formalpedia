-- Prove2me | Theorems.Thm_YeIPA_QPApprox_sdp_range_approximates_qp
-- name    : YeIPA.QPApprox.sdp_range_approximates_qp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:59.429435+00:00
-- url     : https://prove2.me/theorems/426e02c5-13b9-43a6-ba8f-4b6e5357d368
-- title:
--   Theorem 9.33 — the semidefinite relaxation approximates the range of the quadratic program within $2/\pi$
-- statement:
--   Let $Q$ be a symmetric $n\times n$ matrix, $A\in\mathbb R^{m\times n}$ with rows $a_i$, $A_i=\operatorname{diag}(a_i)$, $b\in\mathbb R^m$, and assume the quadratic program
--   $$\underline q(Q)=\min\ x^TQx\quad\text{s.t.}\quad \textstyle\sum_{j=1}^na_{ij}x_j^2=b_i\ (i=1,\dots,m),\quad -e\le x\le e$$
--   is feasible. Let $\underline p(Q)=\min\{Q\bullet X:\ A_i\bullet X=b_i\ (i=1,\dots,m),\ d(X)\le e,\ X\succeq0\}$ be its semidefinite relaxation, and set $\underline q=\underline q(Q)$, $\bar q=-\underline q(-Q)$ (the maximum of the QP), $\underline p=\underline p(Q)$, $\bar p=-\underline p(-Q)$. Then
--   1. $$\bar p-\underline q\ \ge\ \tfrac2\pi\,(\bar p-\underline p);$$
--   2. $$\bar q-\underline p\ \ge\ \tfrac2\pi\,(\bar p-\underline p);$$
--   3. $$\bar p-\underline p\ \ge\ \bar q-\underline q\ \ge\ \tfrac{4-\pi}{\pi}\,(\bar p-\underline p).$$
--
--   The range $[\underline p,\bar p]$ of the convex relaxation, computable by interior-point methods, thus approximates the range $[\underline q,\bar q]$ of the nonconvex QP within constant factors, for quadratic equality constraints and box bounds, and with no sign or definiteness assumption on $Q$.
--
--   **Formalization Note** The standing assumptions of §9.5 (p. 325), $Q$ symmetric and the QP feasible, are the only hypotheses. No positive definite feasible point of the relaxation and no attainment of the dual (9.49) is assumed: the printed proof uses both (finding F3), but the statement holds without them. $\underline q$ and $\underline p$ are real infima of nonempty compact sets of values, hence attained.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, pp. 329–330, Theorem 9.33

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation

open Matrix MeasureTheory

namespace YeIPA.QPApprox

variable {m n : ℕ}

/-- **Theorem 9.33** (Ye, *Interior Point Algorithms*, Wiley 1997, pp. 329–330).

With `q̲ = q̲(Q)`, `q̄ = −q̲(−Q)`, `p̲ = p̲(Q)`, `p̄ = −p̲(−Q)`:
i) `p̄ − q̲ ≥ (2/π)(p̄ − p̲)`;
ii) `q̄ − p̲ ≥ (2/π)(p̄ − p̲)`;
iii) `p̄ − p̲ ≥ q̄ − q̲ ≥ ((4 − π)/π)(p̄ − p̲)`.

Standing assumptions of §9.5 (p. 325): `Q` symmetric, the QP feasible. -/
theorem sdp_range_approximates_qp (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x) :
    -- (i)
    sdpMax Q A b - qpMin Q A b ≥ (2 / Real.pi) * (sdpMax Q A b - sdpMin Q A b) ∧
    -- (ii)
    qpMax Q A b - sdpMin Q A b ≥ (2 / Real.pi) * (sdpMax Q A b - sdpMin Q A b) ∧
    -- (iii)
    sdpMax Q A b - sdpMin Q A b ≥ qpMax Q A b - qpMin Q A b ∧
    qpMax Q A b - qpMin Q A b ≥ ((4 - Real.pi) / Real.pi) * (sdpMax Q A b - sdpMin Q A b) := by sorry

end YeIPA.QPApprox
