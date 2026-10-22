-- Prove2me | Theorems.Thm_YeIPA_LP_primal_potential_step
-- name    : YeIPA.LP.primal_potential_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:25.028746+00:00
-- url     : https://prove2.me/theorems/827559c5-9ac3-4617-9c9c-0018eee2bfb3
-- title:
--   p. 122, display after (4.10) — the step (4.10) lowers $\mathcal P_{n+\rho}$ by $\alpha\|p^k\|-\alpha^2/(2(1-\alpha))$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$, $n\ge1$, $b\ne0$, and let (LP) and (LD) have interior feasible points. Let $(x^k,y^k,s^k)\in\mathring{\mathcal F}$, i.e. $Ax^k=b$, $x^k>0$, $A^Ty^k+s^k=c$, $s^k>0$; let $\rho=\sqrt n$ and $z^k=b^Ty^k$. With $\mathcal P_{n+\rho}(x,z)=(n+\rho)\log(c^Tx-z)-\sum_j\log x_j$ and
--   $$p^k=(I-X^kA^T(A(X^k)^2A^T)^{-1}AX^k)\,X^k\nabla\mathcal P_{n+\rho}(x^k,z^k),\qquad x^{k+1}=x^k-\alpha\frac{X^kp^k}{\|p^k\|}\quad(4.10),$$
--   where $0<\alpha<1$, one has
--   $$\mathcal P_{n+\rho}(x^{k+1},z^k)-\mathcal P_{n+\rho}(x^k,z^k)\le-\alpha\|p^k\|+\frac{\alpha^2}{2(1-\alpha)}.$$
--
--   This is the estimate used in Theorem 4.9 when $\|p^k\|$ is large: the primal step then lowers the primal, and hence the primal-dual, potential by a constant.
--
--   **Formalization Note** The book states this display "in view of Section 3.3.2" without a number; the hypotheses are those of §4.3 ($\rho=\sqrt n$, p. 121; $(x^k,y^k,s^k)\in\mathring{\mathcal F}$, p. 121) and the constant $0<\alpha<1$ of Section 3.3.2. The standing assumptions (rank $m$, interior points, p. 63; $b\ne0$, p. 109) and $n\ge1$ are explicit hypotheses. When $p^k=0$ the book's step is undefined; Lean's division by $0$ gives $x^{k+1}=x^k$, where the inequality also holds.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 122, display following (4.10)

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix

namespace YeIPA.LP

/-- Ye 1997, p. 122, the display following (4.10). Under the standing assumptions (p. 63), let
`(xᵏ, yᵏ, sᵏ) ∈ F̊`, `ρ = √n` (§4.3, p. 121), `zᵏ = bᵀyᵏ`, `0 < α < 1`, and let `xᵏ⁺¹` be the
step (4.10). Then `P_{n+ρ}(xᵏ⁺¹, zᵏ) − P_{n+ρ}(xᵏ, zᵏ) ≤ −α‖pᵏ‖ + α²/(2(1 − α))`. -/
theorem primal_potential_step {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hA : StandingAssumptions A b c)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hF : IsInteriorFeasible A b c x y s)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    primalPotential (Real.sqrt n) c (primalStep A c (Real.sqrt n) α x (b ⬝ᵥ y)) (b ⬝ᵥ y) -
        primalPotential (Real.sqrt n) c x (b ⬝ᵥ y) ≤
      -α * norm2 (pVec A c (Real.sqrt n) x (b ⬝ᵥ y)) + α ^ 2 / (2 * (1 - α)) := by sorry

end YeIPA.LP
