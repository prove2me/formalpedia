-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_eq_57
-- name    : WorstCaseCVaR.Mixture.eq_57
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:18.511449+00:00
-- url     : https://prove2.me/theorems/a3e5c552-58d3-4ad7-8c9d-12697b20d2a0
-- title:
--   (57) — $\mathrm{WCVaR}_\beta(x)=\min_{\alpha}\max_{\lambda\in\Lambda}\sum_i\lambda_iF^i_\beta(x,\alpha)$
-- statement:
--   Under the standing assumptions ($l\ge1$ probability distributions $P^i$, $f(x,\cdot)$ integrable under each, $0<\beta<1$), the function $\alpha\mapsto\max_{\lambda\in\Lambda}H_\beta(x,\alpha,\lambda)$ attains its minimum over $\mathbb R$ at some $\alpha_0$, and
--   $$\mathrm{WCVaR}_\beta(x)=\min_{\alpha\in\mathbb R}\max_{\lambda\in\Lambda}H_\beta(x,\alpha,\lambda)=\min_{\alpha\in\mathbb R}\max_{\lambda\in\Lambda}\sum_{i=1}^l\lambda_iF^i_\beta(x,\alpha);$$
--   moreover $\max_{\lambda\in\Lambda}H_\beta(x,\alpha,\lambda)=\max_{\lambda\in\Lambda}\sum_i\lambda_iF^i_\beta(x,\alpha)$ for every $\alpha$.
--
--   This is the min–max form of the worst-case CVaR; the paper obtains it from (55), the inequality (56) and the elementary min–max inequality.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1167, proof of Theorem 1, Eq. (56)–(57)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem eq_57 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    ∃ α₀ : ℝ,
      IsMinOn (fun α => sSup ((fun lam => Hfun P f β x α lam) '' stdSimplex ℝ (Fin l)))
          Set.univ α₀ ∧
        wcvar P f β x = sSup ((fun lam => Hfun P f β x α₀ lam) '' stdSimplex ℝ (Fin l)) ∧
        ∀ α : ℝ, sSup ((fun lam => Hfun P f β x α lam) '' stdSimplex ℝ (Fin l)) =
          sSup ((fun lam => ∑ i, lam i * Fi P f β x i α) '' stdSimplex ℝ (Fin l)) := by sorry

end WorstCaseCVaR.Mixture
