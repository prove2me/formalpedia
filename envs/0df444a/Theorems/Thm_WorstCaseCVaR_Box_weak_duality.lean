-- Prove2me | Theorems.Thm_WorstCaseCVaR_Box_weak_duality
-- name    : WorstCaseCVaR.Box.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:23.848199+00:00
-- url     : https://prove2.me/theorems/248f983e-9913-446e-928e-3197bc31ff50
-- title:
--   Proof of Proposition 2 — weak duality for (22)–(23): $\gamma^*(u)\le\overline\eta^\top\xi+\underline\eta^\top\omega$
-- statement:
--   Let $\underline\eta, \overline\eta, u \in \mathbb R^S$. For every feasible point $\eta$ of the linear program (22) and every feasible point $(z, \xi, \omega)$ of its dual (23) with the same $u$,
--   $$u^\top\eta \le \overline\eta^\top\xi + \underline\eta^\top\omega.$$
--   Consequently, if (22) is feasible, then $\gamma^*(u) \le \overline\eta^\top\xi + \underline\eta^\top\omega$ for every feasible $(z, \xi, \omega)$ of (23).
--
--   This is the inequality used in the first half of the proof of Proposition 2 to show that a feasible point of (24)–(30) yields a feasible point of (16)–(20).
--
--   **Formalization Note** The second clause assumes (22) feasible because $\gamma^*$ is a real supremum, whose value on an empty set is the junk value $0$.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1167, proof of Proposition 2

import Mathlib
import Definitions.Def_WorstCaseCVaR_Box_DualPair

open Matrix

namespace WorstCaseCVaR.Box

/-- Proof of Proposition 2, p. 1167: weak duality for the pair (22)–(23). Every feasible `η`
of (22) and every feasible `(z, ξ, ω)` of (23) with the same `u` satisfy
`uᵀη ≤ η̄ᵀξ + η̲ᵀω`; consequently, when (22) is feasible, `γ*(u) ≤ η̄ᵀξ + η̲ᵀω`. -/
theorem weak_duality {S : ℕ} (ηlo ηhi u : Fin S → ℝ) :
    (∀ η ∈ lp22Feasible ηlo ηhi, ∀ d ∈ lp23Feasible u, u ⬝ᵥ η ≤ lp23Obj ηlo ηhi d) ∧
    ((lp22Feasible ηlo ηhi).Nonempty →
      ∀ d ∈ lp23Feasible u, gammaStar ηlo ηhi u ≤ lp23Obj ηlo ηhi d) := by sorry

end WorstCaseCVaR.Box
