-- Prove2me | Theorems.Thm_YeIPA_QPApprox_rounding_approximation_ratio
-- name    : YeIPA.QPApprox.rounding_approximation_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:51.762144+00:00
-- url     : https://prove2.me/theorems/917921f1-81f3-49cf-96c1-d527e589a432
-- title:
--   Theorem 9.35 — the rounding from $\underline X$ satisfies $(\mathbb E_u q(\hat x)-\underline q)/(\bar q-\underline q)\le\pi/2-1<4/7$
-- statement:
--   Let $Q$ be a symmetric $n\times n$ matrix, $A\in\mathbb R^{m\times n}$, $A_i=\operatorname{diag}(a_i)$, $b\in\mathbb R^m$, and assume the QP $\underline q=\underline q(Q)=\min\{x^TQx:\ \sum_ja_{ij}x_j^2=b_i,\ -e\le x\le e\}$ is feasible; let $\bar q=-\underline q(-Q)$ be its maximum. Let $\underline X$ be an optimal solution of the relaxation $\min\{Q\bullet X:\ A_i\bullet X=b_i,\ d(X)\le e,\ X\succeq0\}$, and let $V\in\mathbb R^{n\times n}$ with columns $v_1,\dots,v_n$ satisfy $V^TV=\underline X$. For $u$ uniformly distributed on the unit sphere of $\mathbb R^n$ let
--   $$\hat x=D\,\sigma(V^Tu),\qquad D=\operatorname{diag}(\|v_1\|,\dots,\|v_n\|),$$
--   where $\sigma(w)_j=\operatorname{sign}(w_j)$, $\operatorname{sign}(t)=1$ for $t\ge0$ and $-1$ otherwise. Then, with $q(x)=x^TQx$,
--   $$\frac{\mathbb E_u\,q(\hat x)-\underline q}{\bar q-\underline q}\ \le\ \frac\pi2-1\ <\ \frac47 .$$
--
--   Each $\hat x$ is feasible for the QP, so the randomized rounding is a $(\pi/2-1)$-approximate minimizer in expectation.
--
--   **Formalization Note** The standing assumptions of §9.5 (p. 325), $Q$ symmetric and the QP feasible, are hypotheses. "Randomly generated from $\underline X$" is (9.50) with any factor $V$ of $\underline X$; $D=\operatorname{diag}(\|v_j\|)=\operatorname{diag}(\sqrt{\underline x_{jj}})$. The expectation is the integral against the normalized surface measure on the unit sphere. Division is real division, so when $\bar q=\underline q$ (e.g. $Q=0$), where the book's quotient is undefined, the left side is $0$ and the inequality holds trivially; no hypothesis $\bar q>\underline q$ is added.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 331, Theorem 9.35

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation

open Matrix MeasureTheory

namespace YeIPA.QPApprox

variable {m n : ℕ}

/-- **Theorem 9.35** (Ye, *Interior Point Algorithms*, Wiley 1997, p. 331).

Let `X̲` be an optimal solution of the relaxation (9.48), `X̲ = V̲ᵀV̲` with `V̲ ∈ ℝ^{n×n}`, and let
`x̂ = D̲σ(V̲ᵀu)` (9.50), `D̲ = diag(‖v̲_1‖, …, ‖v̲_n‖)`, with `u` uniform on the unit sphere of
`ℝⁿ`. Then `(E_u q(x̂) − q̲)/(q̄ − q̲) ≤ π/2 − 1 < 4/7`.

Standing assumptions of §9.5 (p. 325): `Q` symmetric, the QP feasible. Real division: when
`q̄ = q̲` the left side is `0` in Lean (the book's quotient is undefined there). -/
theorem rounding_approximation_ratio (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x)
    (X V : Matrix (Fin n) (Fin n) ℝ) (hX : IsRelaxOptimal Q A b X) (hV : Vᵀ * V = X) :
    ((∫ u, quadForm Q (roundedPoint V u) ∂(sphereUniform n)) - qpMin Q A b) /
        (qpMax Q A b - qpMin Q A b) ≤ Real.pi / 2 - 1 ∧
      Real.pi / 2 - 1 < 4 / 7 := by sorry

end YeIPA.QPApprox
