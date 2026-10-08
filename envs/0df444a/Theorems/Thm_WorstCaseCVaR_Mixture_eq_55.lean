-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_eq_55
-- name    : WorstCaseCVaR.Mixture.eq_55
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:52.759823+00:00
-- url     : https://prove2.me/theorems/70ce3d70-0e19-4f8e-9885-c0c8df6a6a25
-- title:
--   (55) — $\max_\lambda\min_{\mathbb R}H_\beta=\max_\lambda\min_{\mathcal A}H_\beta=\min_{\mathcal A}\max_\lambda H_\beta$
-- statement:
--   Under the standing assumptions and with $\mathcal A=[\min_i\underline\alpha^*_i,\max_i\overline\alpha^*_i]$ built from the minimizer intervals of the $F^i_\beta(x,\cdot)$ as in the previous milestone, there are $\alpha_0\in\mathcal A$ and $\lambda_0\in\Lambda$ such that $H_\beta(x,\alpha_0,\lambda_0)$ is simultaneously
--
--   1. the largest value of $\lambda\mapsto\inf_{\alpha\in\mathbb R}H_\beta(x,\alpha,\lambda)$ over $\Lambda$,
--   2. the largest value of $\lambda\mapsto\min_{\alpha\in\mathcal A}H_\beta(x,\alpha,\lambda)$ over $\Lambda$,
--   3. the smallest value of $\alpha\mapsto\max_{\lambda\in\Lambda}H_\beta(x,\alpha,\lambda)$ over $\mathcal A$.
--
--   That is,
--   $$\max_{\lambda\in\Lambda}\min_{\alpha\in\mathbb R}H_\beta(x,\alpha,\lambda)=\max_{\lambda\in\Lambda}\min_{\alpha\in\mathcal A}H_\beta(x,\alpha,\lambda)=\min_{\alpha\in\mathcal A}\max_{\lambda\in\Lambda}H_\beta(x,\alpha,\lambda).$$
--
--   **Formalization Note** The inner extrema are the real `sInf`/`sSup` of images; each is attained under the hypotheses, and the outer extrema are stated as `IsGreatest`/`IsLeast` with the common value exhibited.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1166, proof of Theorem 1, Eq. (55)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem eq_55 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i))
    (a b : Fin l → ℝ)
    (hab : ∀ i, {α : ℝ | IsMinOn (Fi P f β x i) Set.univ α} = Set.Icc (a i) (b i)) :
    ∃ α₀ ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
        (Finset.univ.sup' Finset.univ_nonempty b),
      ∃ lam₀ ∈ stdSimplex ℝ (Fin l),
        IsGreatest ((fun lam => sInf (Set.range (fun α => Hfun P f β x α lam))) ''
            stdSimplex ℝ (Fin l)) (Hfun P f β x α₀ lam₀) ∧
        IsGreatest ((fun lam => sInf ((fun α => Hfun P f β x α lam) ''
            Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
              (Finset.univ.sup' Finset.univ_nonempty b))) ''
            stdSimplex ℝ (Fin l)) (Hfun P f β x α₀ lam₀) ∧
        IsLeast ((fun α => sSup ((fun lam => Hfun P f β x α lam) '' stdSimplex ℝ (Fin l))) ''
            Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
              (Finset.univ.sup' Finset.univ_nonempty b)) (Hfun P f β x α₀ lam₀) := by sorry

end WorstCaseCVaR.Mixture
