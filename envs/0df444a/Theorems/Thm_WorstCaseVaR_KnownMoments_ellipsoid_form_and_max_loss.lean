-- Prove2me | Theorems.Thm_WorstCaseVaR_KnownMoments_ellipsoid_form_and_max_loss
-- name    : WorstCaseVaR.KnownMoments.ellipsoid_form_and_max_loss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:16:08.603984+00:00
-- url     : https://prove2.me/theorems/89be9fd1-25ca-48b5-bd16-033e0dfb706b
-- title:
--   §2.1, p. 546 — Condition (10) is an ellipsoid, and the worst-case VaR is the maximal loss over it
-- statement:
--   Let $\hat x, w \in \mathbb R^n$, let $\Gamma \succ 0$ and let $0 < \varepsilon \le 1$, with $\kappa(\varepsilon) = \sqrt{(1-\varepsilon)/\varepsilon}$.
--
--   1. For every $x \in \mathbb R^n$, Condition (10),
--   $$\begin{bmatrix}\Gamma & x - \hat x\\ (x-\hat x)^\top & \kappa(\varepsilon)^2\end{bmatrix} \succeq 0,$$
--   holds if and only if $x$ lies in the ellipsoid $\mathcal E = \{x \mid (x - \hat x)^\top \Gamma^{-1}(x - \hat x) \le \kappa(\varepsilon)^2\}$.
--   2. The maximal loss over this set is attained and equals
--   $$\max\{-x^\top w \;:\; x \text{ satisfies (10)}\} = \kappa(\varepsilon)\sqrt{w^\top\Gamma w} - \hat x^\top w.$$
--
--   This is the "game-theoretic" reading of the worst-case VaR: it is the largest loss $-x^\top w$ when the return vector is deterministic and only known to lie in $\mathcal E$. It links Propositions 2 and 4 of Theorem 1.
--
--   **Formalization Note.** The maximum is stated with `IsGreatest`; $\Gamma^{-1}$ is the matrix inverse, well defined since $\Gamma \succ 0$.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 546, §2.1, comments after Theorem 1 (V_𝒫(w) = max −x^T w subject to Condition (10); the ellipsoid ℰ)

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- The ellipsoid form of Condition (10) (p. 546): with `Γ ≻ 0`,
`[[Γ, x - x̂], [(x - x̂)ᵀ, κ(ε)²]] ⪰ 0` iff `(x - x̂)ᵀ Γ⁻¹ (x - x̂) ≤ κ(ε)²`, and the maximal loss
`-xᵀw` over the `x` satisfying (10) is `κ(ε) √(wᵀΓw) - x̂ᵀw`. -/
theorem ellipsoid_form_and_max_loss {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ x : EuclideanSpace ℝ (Fin n),
        (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef ↔
          ⇑(x - xhat) ⬝ᵥ Γ⁻¹ *ᵥ ⇑(x - xhat) ≤ kappa ε ^ 2) ∧
    IsGreatest {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin n),
        (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef ∧ r = -⟪x, w⟫_ℝ}
      (kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ) := by sorry

end WorstCaseVaR.KnownMoments
