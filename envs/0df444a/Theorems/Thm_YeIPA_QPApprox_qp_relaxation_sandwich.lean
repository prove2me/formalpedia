-- Prove2me | Theorems.Thm_YeIPA_QPApprox_qp_relaxation_sandwich
-- name    : YeIPA.QPApprox.qp_relaxation_sandwich
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:39.751399+00:00
-- url     : https://prove2.me/theorems/452fbc1f-7989-4696-a073-58e53ea8b3c2
-- title:
--   Proposition 9.29 — $\underline p\le\underline q\le\bar q\le\bar p$, and the dual description of $\bar p$
-- statement:
--   Let $Q$ be a symmetric $n\times n$ matrix, $A\in\mathbb R^{m\times n}$ with rows $a_i$, $A_i=\operatorname{diag}(a_i)$, $b\in\mathbb R^m$, and assume the QP
--   $$\underline q(Q)=\min\ x^TQx\quad\text{s.t.}\quad \textstyle\sum_{j}a_{ij}x_j^2=b_i\ (i=1,\dots,m),\quad -e\le x\le e$$
--   is feasible. Let $\underline p(Q)=\min\{Q\bullet X: A_i\bullet X=b_i,\ d(X)\le e,\ X\succeq0\}$ be the value of the semidefinite relaxation (9.48), and set $\underline q=\underline q(Q)$, $\bar q=-\underline q(-Q)$, $\underline p=\underline p(Q)$, $\bar p=-\underline p(-Q)$. Then:
--
--   1. $\bar q$ is the maximal value of $x^TQx$ over the feasible set of the QP (it bounds every feasible value and is attained).
--   2. $\bar p$ is the maximal value of $Q\bullet X$ over the feasible set of the relaxation (it bounds every feasible value and is attained). Moreover, if $(\underline y(-Q),\underline z(-Q))$ is an optimal solution of the dual (9.49) written for $-Q$, i.e. of $\max\{e^Tz+b^Ty:\ -Q\succeq D(z)+\sum_iy_iA_i,\ z\le0\}$, and $(\bar y,\bar z)=(-\underline y(-Q),-\underline z(-Q))$, then $\bar p=e^T\bar z+b^T\bar y$ and $D(\bar z)+\sum_{i=1}^m\bar y_iA_i-Q\succeq0$.
--   3. $$\underline p\le\underline q\le\bar q\le\bar p .$$
--
--   Part 3 says the relaxation brackets the range of the QP; part 2 supplies the dual certificate used in the proof of Theorem 9.33.
--
--   **Formalization Note** The standing assumptions of §9.5 (p. 325), $Q$ symmetric and the QP feasible, are hypotheses. The book asserts on p. 326 that the dual has an optimal solution and names it; that existence can fail (finding F2), so the two clauses of part 2 that name $(\bar y,\bar z)$ are stated for every dual optimal pair of the problem for $-Q$; the maximality of $\bar p$ and parts 1 and 3 do not depend on it. "Maximal value" is stated as "an upper bound that is attained".
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 326, Proposition 9.29

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation

open Matrix MeasureTheory

namespace YeIPA.QPApprox

variable {m n : ℕ}

/-- **Proposition 9.29** (Ye, *Interior Point Algorithms*, Wiley 1997, p. 326).

Let `q̲ := q̲(Q)`, `q̄ := −q̲(−Q)`, `p̲ := p̲(Q)`, `p̄ := −p̲(−Q)`, and
`(ȳ, z̄) = (−y̲(−Q), −z̲(−Q))` for an optimal solution `(y̲(−Q), z̲(−Q))` of the dual (9.49)
written for `−Q`. Then
i) `q̄` is the maximal objective value of `xᵀQx` in the feasible set of the QP;
ii) `p̄ = eᵀz̄ + bᵀȳ`, it is the maximal objective value of `Q • X` in the feasible set of
the relaxation, and `D(z̄) + ∑ ȳ_i A_i − Q ⪰ 0`;
iii) `p̲ ≤ q̲ ≤ q̄ ≤ p̄`.

In (ii) the maximality of `p̄` is asserted outright; the two clauses that name `(ȳ, z̄)` are
asserted for every optimal dual pair, since the page names one without proving it exists
(FINDINGS.yaml F2).

Standing assumptions of §9.5 (p. 325): `Q` symmetric, the QP feasible. -/
theorem qp_relaxation_sandwich (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x) :
    -- (i)
    ((∀ x, IsQPFeasible A b x → quadForm Q x ≤ qpMax Q A b) ∧
      ∃ x, IsQPFeasible A b x ∧ quadForm Q x = qpMax Q A b) ∧
    -- (ii)
    ((∀ X, IsRelaxFeasible A b X → frob Q X ≤ sdpMax Q A b) ∧
      (∃ X, IsRelaxFeasible A b X ∧ frob Q X = sdpMax Q A b) ∧
      ∀ (y : Fin m → ℝ) (z : Fin n → ℝ), IsDualOptimal (-Q) A b y z →
        sdpMax Q A b = dualObj b (-y) (-z) ∧
        (diagMat (-z) + ∑ i, (-y) i • constrMat A i - Q).PosSemidef) ∧
    -- (iii)
    (sdpMin Q A b ≤ qpMin Q A b ∧ qpMin Q A b ≤ qpMax Q A b ∧ qpMax Q A b ≤ sdpMax Q A b) := by sorry

end YeIPA.QPApprox
