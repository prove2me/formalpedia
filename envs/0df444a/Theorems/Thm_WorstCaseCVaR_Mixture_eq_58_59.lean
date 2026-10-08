-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_eq_58_59
-- name    : WorstCaseCVaR.Mixture.eq_58_59
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:28.318301+00:00
-- url     : https://prove2.me/theorems/7add36e7-341c-49ec-87cb-39e1eae29fca
-- title:
--   (58)–(59) — $\sum_i\lambda_iF^i_\beta\le\theta\ \forall\lambda\in\Lambda$ iff $F^i_\beta\le\theta\ \forall i$
-- statement:
--   Under the standing assumptions, for all $\alpha,\theta\in\mathbb R$,
--   $$\sum_{i=1}^l\lambda_iF^i_\beta(x,\alpha)\le\theta\ \ \text{for all }\lambda\in\Lambda\quad\Longleftrightarrow\quad F^i_\beta(x,\alpha)\le\theta\ \ \text{for } i=1,\dots,l,$$
--   and consequently, for every $\alpha$,
--   $$\max_{\lambda\in\Lambda}\sum_{i=1}^l\lambda_iF^i_\beta(x,\alpha)=\max_{i\in\mathcal L}F^i_\beta(x,\alpha)=F^{\mathcal L}_\beta(x,\alpha).$$
--
--   This identifies the epigraph problem (58) with the right-hand side of (6).
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1167, proof of Theorem 1, Eq. (58)–(59)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem eq_58_59 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    (∀ α θ : ℝ, (∀ lam ∈ stdSimplex ℝ (Fin l), ∑ i, lam i * Fi P f β x i α ≤ θ) ↔
        ∀ i, Fi P f β x i α ≤ θ) ∧
      ∀ α : ℝ, sSup ((fun lam => ∑ i, lam i * Fi P f β x i α) '' stdSimplex ℝ (Fin l)) =
        FL P f β x α := by sorry

end WorstCaseCVaR.Mixture
