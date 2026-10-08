-- Prove2me | Theorems.Thm_WorstCaseCVaR_Box_max_decomposition
-- name    : WorstCaseCVaR.Box.max_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:06.177043+00:00
-- url     : https://prove2.me/theorems/8baf5f45-ae1c-482f-8574-a0f0531acb9e
-- title:
--   p. 1159 — $\max_{\pi\in\mathcal P_\pi^B}\alpha+\frac{1}{1-\beta}\pi^\top u=\alpha+\frac{1}{1-\beta}(\pi^0)^\top u+\frac{\gamma^*(u)}{1-\beta}$
-- statement:
--   Let $0 < \beta < 1$, $\alpha \in \mathbb R$, $u \in \mathbb R^S$, and let $\pi^0, \underline\eta, \overline\eta \in \mathbb R^S$ define the box uncertainty set $\mathcal P_\pi^B$ of (21). Suppose the linear program (22),
--   $$\max_{\eta \in \mathbb R^S}\{u^\top\eta : e^\top\eta = 0,\ \underline\eta \le \eta \le \overline\eta\},$$
--   is feasible. Then (22) attains its optimal value $\gamma^*(u)$, and the maximum of $\alpha + \frac{1}{1-\beta}\pi^\top u$ over $\pi \in \mathcal P_\pi^B$ is attained and equals
--   $$\max_{\pi \in \mathcal P_\pi^B} \alpha + \frac{1}{1-\beta}\pi^\top u = \alpha + \frac{1}{1-\beta}(\pi^0)^\top u + \frac{\gamma^*(u)}{1-\beta}.$$
--
--   This reduces the worst-case constraint (18) over the box to the optimal value of a single linear program, which is the first step toward the LP reformulation (24)–(30).
--
--   **Formalization Note** "Attained maximum with value $v$" is `IsGreatest` of the image set. Feasibility of (22) is assumed; it is equivalent to nonemptiness of $\mathcal P_\pi^B$.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1159, display preceding Eq. (22)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Box_DualPair

open Matrix

namespace WorstCaseCVaR.Box

/-- p. 1159, display before (22): if (22) is feasible, then (22) attains its optimal value
`γ*(u)`, and `max_{π ∈ 𝒫_π^B} α + (1 − β)⁻¹ πᵀu` exists and equals
`α + (1 − β)⁻¹ (π⁰)ᵀu + γ*(u)/(1 − β)`. -/
theorem max_decomposition {S : ℕ} (β α : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (π0 ηlo ηhi u : Fin S → ℝ) (hfeas : (lp22Feasible ηlo ηhi).Nonempty) :
    IsGreatest ((fun η => u ⬝ᵥ η) '' lp22Feasible ηlo ηhi) (gammaStar ηlo ηhi u) ∧
    IsGreatest ((fun π => α + (1 - β)⁻¹ * (π ⬝ᵥ u)) '' boxSet π0 ηlo ηhi)
      (α + (1 - β)⁻¹ * (π0 ⬝ᵥ u) + gammaStar ηlo ηhi u / (1 - β)) := by sorry

end WorstCaseCVaR.Box
