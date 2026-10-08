-- Prove2me | Theorems.Thm_WorstCaseCVaR_Box_strong_duality
-- name    : WorstCaseCVaR.Box.strong_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:20.695726+00:00
-- url     : https://prove2.me/theorems/ece9507a-3a92-4f17-8b50-60256379f76f
-- title:
--   Proof of Proposition 2 — strong duality for (22)–(23): (23) has an optimal solution with value $\gamma^*(u)$
-- statement:
--   Let $\underline\eta, \overline\eta, u \in \mathbb R^S$ and suppose the linear program (22),
--   $$\max_{\eta \in \mathbb R^S}\{u^\top\eta : e^\top\eta = 0,\ \underline\eta \le \eta \le \overline\eta\},$$
--   is feasible. Then its dual (23),
--   $$\min_{(z,\xi,\omega) \in \mathbb R \times \mathbb R^S \times \mathbb R^S}\{\overline\eta^\top\xi + \underline\eta^\top\omega : e z + \xi + \omega = u,\ \xi \ge 0,\ \omega \le 0\},$$
--   has an optimal solution, and every optimal solution $(z^*, \xi^*, \omega^*)$ satisfies
--   $$\overline\eta^\top\xi^* + \underline\eta^\top\omega^* = \gamma^*(u).$$
--
--   This is the strong duality step of the proof of Proposition 2: it lets the worst-case constraint (18) be replaced by the explicit linear constraints (26)–(28).
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1167, proof of Proposition 2

import Mathlib
import Definitions.Def_WorstCaseCVaR_Box_DualPair

open Matrix

namespace WorstCaseCVaR.Box

/-- Proof of Proposition 2, p. 1167: strong duality for the pair (22)–(23). If (22) is
feasible, then (23) has an optimal solution, and the optimal value of (23) equals `γ*(u)`. -/
theorem strong_duality {S : ℕ} (ηlo ηhi u : Fin S → ℝ)
    (hfeas : (lp22Feasible ηlo ηhi).Nonempty) :
    (∃ d, IsOptimal23 ηlo ηhi u d) ∧
    ∀ d, IsOptimal23 ηlo ηhi u d → lp23Obj ηlo ηhi d = gammaStar ηlo ηhi u := by sorry

end WorstCaseCVaR.Box
