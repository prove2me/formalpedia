-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_eq_54
-- name    : WorstCaseCVaR.Mixture.eq_54
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:51.677916+00:00
-- url     : https://prove2.me/theorems/7f77bf28-bd60-41f6-9ce5-bad417c58128
-- title:
--   (54) — $\mathrm{WCVaR}_\beta(x)=\max_{\lambda\in\Lambda}\min_{\alpha}H_\beta(x,\alpha,\lambda)$, both attained
-- statement:
--   Under the standing assumptions ($l\ge1$ probability distributions $P^i$, $f(x,\cdot)$ integrable under each, $0<\beta<1$):
--
--   1. for every $\lambda\in\Lambda$ the minimum of $\alpha\mapsto H_\beta(x,\alpha,\lambda)$ is attained at some $\alpha_0$, its value is $\mathrm{CVaR}_\beta(x)$ under the mixture $\sum_i\lambda_iP^i$, and $H_\beta(x,\alpha_0,\lambda)=\sum_i\lambda_iF^i_\beta(x,\alpha_0)$;
--   2. the supremum defining $\mathrm{WCVaR}_\beta(x)$ is attained: $\mathrm{WCVaR}_\beta(x)$ is the largest of the values $\mathrm{CVaR}_\beta(x)$ over mixtures with $\lambda\in\Lambda$.
--
--   Together,
--   $$\mathrm{WCVaR}_\beta(x)=\max_{\lambda\in\Lambda}\min_{\alpha\in\mathbb R}H_\beta(x,\alpha,\lambda)=\max_{\lambda\in\Lambda}\min_{\alpha\in\mathbb R}\sum_{i=1}^l\lambda_iF^i_\beta(x,\alpha).$$
--
--   This is the max–min form of the worst-case CVaR from which the minimax argument starts.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1166, proof of Theorem 1, Eq. (54)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem eq_54 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    (∀ lam ∈ stdSimplex ℝ (Fin l), ∃ α₀ : ℝ,
        IsMinOn (fun α => Hfun P f β x α lam) Set.univ α₀ ∧
        cvar (mixture P lam) f β x = Hfun P f β x α₀ lam ∧
        Hfun P f β x α₀ lam = ∑ i, lam i * Fi P f β x i α₀) ∧
    IsGreatest ((fun lam => cvar (mixture P lam) f β x) '' stdSimplex ℝ (Fin l))
      (wcvar P f β x) := by sorry

end WorstCaseCVaR.Mixture
