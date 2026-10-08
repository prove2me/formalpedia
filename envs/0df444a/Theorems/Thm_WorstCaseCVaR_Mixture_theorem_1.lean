-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_theorem_1
-- name    : WorstCaseCVaR.Mixture.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:17.969524+00:00
-- url     : https://prove2.me/theorems/79d6ecb1-fb26-451e-9101-a37b35162a46
-- title:
--   Theorem 1 — under mixture uncertainty, $\mathrm{WCVaR}_\beta(x)=\min_{\alpha}\max_{i}F^i_\beta(x,\alpha)$
-- statement:
--   Let $P^1,\dots,P^l$ ($l\ge1$) be probability distributions on $\mathbb R^m$ (the likelihood distributions), let $0<\beta<1$, and let $x\in\mathbb R^n$ be a decision for which the loss $f(x,\cdot)$ is integrable under every $P^i$. Then the worst-case CVaR of $x$ over the set $\mathcal P_M$ of all mixtures $\sum_i\lambda_iP^i$, $\lambda\in\Lambda$, is
--   $$\mathrm{WCVaR}_\beta(x)=\min_{\alpha\in\mathbb R}\max_{i\in\mathcal L}F^i_\beta(x,\alpha),\qquad \mathcal L=\{1,\dots,l\},$$
--   where $F^i_\beta(x,\alpha)=\alpha+\frac1{1-\beta}\int[f(x,y)-\alpha]^+\,dP^i(y)$, and the minimum over $\alpha$ is attained.
--
--   The theorem replaces a supremum over infinitely many distributions by a pointwise maximum of $l$ convex functions, so worst-case CVaR minimization over mixtures is a single convex program in $(x,\alpha)$.
--
--   **Formalization Note** The minimum is stated with an explicit minimizer $\alpha_0$ of $F^{\mathcal L}_\beta(x,\cdot)$. Distributions are probability measures (Remark 1 of the paper); indices are zero-based (`Fin l`); $0<\beta<1$ is the standing reading of "confidence level".
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1157, Theorem 1, Eq. (6)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem theorem_1 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    ∃ α₀ : ℝ, IsMinOn (FL P f β x) Set.univ α₀ ∧ wcvar P f β x = FL P f β x α₀ := by sorry

end WorstCaseCVaR.Mixture
