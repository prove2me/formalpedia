-- Prove2me | Theorems.Thm_WorstCaseVaR_KnownMoments_schur_reduction_eq19_eq20
-- name    : WorstCaseVaR.KnownMoments.schur_reduction_eq19_eq20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:15:05.442519+00:00
-- url     : https://prove2.me/theorems/8103ac50-dbe0-4fca-ace8-94ee1f6c8fe9
-- title:
--   §2.1, p. 547, Eqs. (19)–(20) — Schur-complement reduction of the constraints of (18)
-- statement:
--   Let $\hat x \in \mathbb R^n$, let $\Gamma \succ 0$, put $S = \Gamma + \hat x\hat x^\top$ and let $\Sigma = \begin{bmatrix} S & \hat x\\ \hat x^\top & 1\end{bmatrix}$. Let $0 < y < 1$ and $v \in \mathbb R^n$. The following are equivalent:
--
--   1. there is an $n\times n$ matrix $V$ with
--   $$\Sigma \succeq \begin{bmatrix} V & v \\ v^\top & y\end{bmatrix} \succeq 0;$$
--   2. (Eq. (19))
--   $$S \succeq \frac{1}{1-y}(\hat x - v)(\hat x - v)^\top + \frac1y vv^\top;$$
--   3. (Eq. (20))
--   $$\Gamma = S - \hat x\hat x^\top \succeq \frac{1}{y(1-y)}(v - y\hat x)(v - y\hat x)^\top.$$
--
--   This eliminates the matrix variable $V$ from the dual problem (18) of the worst-case VaR SDP, leaving a problem in $(v, y)$ only.
--
--   **Formalization Note.** The chain $\Sigma \succeq B \succeq 0$ is encoded as the two conditions $\Sigma - B \succeq 0$ and $B \succeq 0$. The inequality $A \succeq B$ is `(A - B).PosSemidef`.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 547, §2.1, proof of Theorem 1, Eqs. (18), (19), (20)

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- Eqs. (19)–(20), p. 547: for `0 < y < 1` and `v ∈ ℝⁿ`, the constraint of Problem (18)
`Σ ⪰ [[V, v], [vᵀ, y]] ⪰ 0` holds for some `V` iff
`S ⪰ (1/(1-y))(x̂ - v)(x̂ - v)ᵀ + (1/y)vvᵀ` (19) iff
`Γ = S - x̂x̂ᵀ ⪰ (1/(y(1-y)))(v - yx̂)(v - yx̂)ᵀ` (20). -/
theorem schur_reduction_eq19_eq20 {n : ℕ}
    (xhat : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) (v : EuclideanSpace ℝ (Fin n)) :
    List.TFAE
      [ ∃ V : Matrix (Fin n) (Fin n) ℝ,
          (secondMomentMatrix xhat Γ - bordered V ⇑v y).PosSemidef ∧
            (bordered V ⇑v y).PosSemidef,
        (momentS xhat Γ - (1 / (1 - y)) • vecMulVec ⇑(xhat - v) ⇑(xhat - v)
            - (1 / y) • vecMulVec ⇑v ⇑v).PosSemidef,
        (momentS xhat Γ - vecMulVec ⇑xhat ⇑xhat
            - (1 / (y * (1 - y))) • vecMulVec ⇑(v - y • xhat) ⇑(v - y • xhat)).PosSemidef ] := by sorry

end WorstCaseVaR.KnownMoments
