-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_argmin_interval
-- name    : WorstCaseCVaR.Mixture.argmin_interval
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:55.908606+00:00
-- url     : https://prove2.me/theorems/5bb9bcae-f63a-4c23-9130-9a5ff5e0ad06
-- title:
--   Proof of Theorem 1 — $\arg\min_\alpha F_\beta(x,\alpha)$ is a nonempty closed bounded interval
-- statement:
--   Let $P$ be a probability distribution on $\mathbb R^m$, let $f(x,\cdot)$ be integrable under $P$, and let $0<\beta<1$. Then the set of minimizers of the Rockafellar–Uryasev function $\alpha\mapsto F_\beta(x,\alpha)$ over $\mathbb R$ is a nonempty, closed, bounded interval: there are $\underline\alpha^*\le\overline\alpha^*$ with
--   $$\arg\min_{\alpha\in\mathbb R}F_\beta(x,\alpha)=[\underline\alpha^*,\overline\alpha^*].$$
--
--   Applied to each likelihood distribution $P^i$, this gives the intervals $[\underline\alpha^*_i,\overline\alpha^*_i]$ used to localize the minimization in the proof of Theorem 1.
--
--   **Formalization Note** Both bounds on $\beta$ matter: at $\beta=0$ the minimizer set can be a half-line.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1166, proof of Theorem 1 (citing Rockafellar and Uryasev 2000, 2002)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem argmin_interval {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) :
    ∃ a b : ℝ, a ≤ b ∧ {α : ℝ | IsMinOn (ruFun P f β x) Set.univ α} = Set.Icc a b := by sorry

end WorstCaseCVaR.Mixture
