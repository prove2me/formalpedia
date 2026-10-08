-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_eq_53
-- name    : WorstCaseCVaR.Mixture.eq_53
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:44.991972+00:00
-- url     : https://prove2.me/theorems/455c4968-8b89-46bd-a093-92dced436c13
-- title:
--   (53) — $H_\beta(x,\alpha,\lambda)=\sum_i\lambda_iF^i_\beta(x,\alpha)$
-- statement:
--   Let $P^1,\dots,P^l$ ($l\ge1$) be probability distributions on $\mathbb R^m$, let $f(x,\cdot)$ be integrable under each $P^i$, and let $0<\beta<1$. For every weight vector $\lambda$ in the simplex $\Lambda$ and every $\alpha\in\mathbb R$, the Rockafellar–Uryasev function of the mixture $\sum_i\lambda_iP^i$ is the $\lambda$-weighted sum of the component functions:
--   $$H_\beta(x,\alpha,\lambda)=\alpha+\frac1{1-\beta}\int[f(x,y)-\alpha]^+\,d\Big(\sum_{i=1}^l\lambda_iP^i\Big)(y)=\sum_{i=1}^l\lambda_iF^i_\beta(x,\alpha).$$
--
--   This identity turns the worst-case problem over mixtures into a problem that is affine in the weights $\lambda$.
--
--   **Formalization Note** $H_\beta$ is `Hfun`, the function (1) evaluated at the measure $\sum_i \lambda_i P^i$; $\Lambda$ is `stdSimplex ℝ (Fin l)`.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1166, proof of Theorem 1, Eq. (53)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem eq_53 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    ∀ lam ∈ stdSimplex ℝ (Fin l), ∀ α : ℝ,
      Hfun P f β x α lam = ∑ i, lam i * Fi P f β x i α := by sorry

end WorstCaseCVaR.Mixture
