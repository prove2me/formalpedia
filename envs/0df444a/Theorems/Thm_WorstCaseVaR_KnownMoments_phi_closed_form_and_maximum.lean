-- Prove2me | Theorems.Thm_WorstCaseVaR_KnownMoments_phi_closed_form_and_maximum
-- name    : WorstCaseVaR.KnownMoments.phi_closed_form_and_maximum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:15:37.304876+00:00
-- url     : https://prove2.me/theorems/7398ea44-208b-4150-8268-7e16325bef1d
-- title:
--   §2.1, p. 547 — $\phi(y)$ in closed form, maximized at $y = \varepsilon$
-- statement:
--   Let $\hat x, w \in \mathbb R^n$, let $\Gamma \succ 0$ and let $0 < \varepsilon \le 1$. Write $\|\Gamma^{1/2}w\|_2 = \sqrt{w^\top\Gamma w}$.
--
--   1. For every $0 < y < 1$, the largest value of $-v^\top w / y$ over the vectors $v \in \mathbb R^n$ satisfying
--   $$\Gamma \succeq \frac{1}{y(1-y)}(v - y\hat x)(v - y\hat x)^\top$$
--   is attained and equals
--   $$\phi(y) = \sqrt{\frac{1-y}{y}}\,\|\Gamma^{1/2}w\|_2 - \hat x^\top w.$$
--   2. Over $y \in [\varepsilon, 1]$, the function $\phi$ (given by the same expression, which at $y=1$ is $-\hat x^\top w$) attains its maximum
--   $$\max_{\varepsilon\le y\le 1}\phi(y) = \sqrt{\frac{1-\varepsilon}{\varepsilon}}\,\|\Gamma^{1/2}w\|_2 - \hat x^\top w = \kappa(\varepsilon)\|\Gamma^{1/2}w\|_2 - \hat x^\top w.$$
--
--   These two facts evaluate the reduced dual problem of the worst-case VaR SDP and produce the closed form (7).
--
--   **Formalization Note.** Both maxima are stated with `IsGreatest`. $\|\Gamma^{1/2}w\|_2$ is written $\sqrt{w^\top\Gamma w}$, which equals it for $\Gamma \succeq 0$.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 547, §2.1, proof of Theorem 1, the displays defining φ(y) and max_{ε≤y≤1} φ(y)

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- The inner value `φ(y)` of the dual problem (p. 547) and its maximum over `y ∈ [ε, 1]`:
(a) for `0 < y < 1`, the maximum of `-vᵀw / y` over `v` with
`Γ ⪰ (1/(y(1-y)))(v - yx̂)(v - yx̂)ᵀ` is `φ(y) = √((1-y)/y) √(wᵀΓw) - x̂ᵀw`;
(b) the maximum of `φ` over `[ε, 1]` is `κ(ε) √(wᵀΓw) - x̂ᵀw`. -/
theorem phi_closed_form_and_maximum {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ y : ℝ, 0 < y → y < 1 →
      IsGreatest {r : ℝ | ∃ v : EuclideanSpace ℝ (Fin n),
          (Γ - (1 / (y * (1 - y))) • vecMulVec ⇑(v - y • xhat) ⇑(v - y • xhat)).PosSemidef ∧
          r = -⟪v, w⟫_ℝ / y}
        (Real.sqrt ((1 - y) / y) * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ)) ∧
    IsGreatest
      ((fun y : ℝ => Real.sqrt ((1 - y) / y) * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ) ''
        Set.Icc ε 1)
      (kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ) := by sorry

end WorstCaseVaR.KnownMoments
