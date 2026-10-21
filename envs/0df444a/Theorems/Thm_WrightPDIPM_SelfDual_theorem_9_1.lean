-- Prove2me | Theorems.Thm_WrightPDIPM_SelfDual_theorem_9_1
-- name    : WrightPDIPM.SelfDual.theorem_9_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:12.052193+00:00
-- url     : https://prove2.me/theorems/dfbfc8de-4ba5-44a9-ac53-3f5d8c40aa2e
-- title:
--   Theorem 9.1 — a feasible self-dual linear program's mLCP (9.2) has a strictly complementary solution
-- statement:
--   Let $M_{11} \in \mathbb R^{p\times p}$ and $M_{22} \in \mathbb R^{q\times q}$ be skew-symmetric ($M_{11} = -M_{11}^{\mathsf T}$, $M_{22} = -M_{22}^{\mathsf T}$), $M_{12} \in \mathbb R^{p\times q}$, $f \in \mathbb R^p$, $g \in \mathbb R^q$, and consider the self-dual linear program
--   $$\min_{u,w} f^{\mathsf T}u + g^{\mathsf T}w \quad\text{s.t.}\quad M_{11}u + M_{12}w \ge -f,\quad -M_{12}^{\mathsf T}u + M_{22}w = -g,\quad u \ge 0,\ w \text{ free}. \qquad (9.1)$$
--   If (9.1) is feasible, then the mixed LCP
--   $$\begin{bmatrix} v\\ 0\end{bmatrix} = \begin{bmatrix} M_{11} & M_{12}\\ -M_{12}^{\mathsf T} & M_{22}\end{bmatrix}\begin{bmatrix} u\\ w\end{bmatrix} + \begin{bmatrix} f\\ g\end{bmatrix},\qquad (u, v) \ge 0,\qquad u^{\mathsf T}v = 0 \qquad (9.2)$$
--   has a strictly complementary solution, that is, a solution $(u, v, w)$ with $u + v > 0$.
--
--   Monotone LCPs need not have strictly complementary solutions; this theorem shows that those coming from self-dual programs always do, which is what interior-point methods for the simplified HSD and HSD forms rely on.
--
--   **Formalization Note** Dimensions $p$, $q$ are arbitrary natural numbers (including $0$).
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 179, Theorem 9.1 (proof pp. 243–245)

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup

namespace WrightPDIPM.SelfDual

open Matrix

/-- Theorem 9.1 (p. 179, proof pp. 243–245): if the self-dual linear program (9.1)
`min fᵀu + gᵀw s.t. M₁₁u + M₁₂w ≥ −f, −M₁₂ᵀu + M₂₂w = −g, u ≥ 0, w free`, with
`M₁₁ = −M₁₁ᵀ` and `M₂₂ = −M₂₂ᵀ` square and skew-symmetric, is feasible, then the mLCP (9.2)
has a strictly complementary solution `(u, v, w)`, i.e. one with `u + v > 0`. -/
theorem theorem_9_1 {p q : ℕ} (M11 : Matrix (Fin p) (Fin p) ℝ) (M12 : Matrix (Fin p) (Fin q) ℝ)
    (M22 : Matrix (Fin q) (Fin q) ℝ) (f : Fin p → ℝ) (g : Fin q → ℝ)
    (hM11 : M11 = -M11ᵀ) (hM22 : M22 = -M22ᵀ)
    (hfeas : SelfDualFeasible M11 M12 M22 f g) :
    ∃ (u v : Fin p → ℝ) (w : Fin q → ℝ),
      IsStrictlyComplementaryMLCP M11 M12 M22 f g u v w := by sorry

end WrightPDIPM.SelfDual
