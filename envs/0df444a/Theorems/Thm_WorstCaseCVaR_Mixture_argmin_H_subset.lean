-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_argmin_H_subset
-- name    : WorstCaseCVaR.Mixture.argmin_H_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:46.37398+00:00
-- url     : https://prove2.me/theorems/4416380d-792e-4248-8ebd-1531c6a1c06d
-- title:
--   Proof of Theorem 1 — $\arg\min_\alpha H_\beta(x,\alpha,\lambda)\subseteq\mathcal A$ and the minimum is attained in $\mathcal A$
-- statement:
--   Under the standing assumptions ($l\ge1$ probability distributions $P^i$, $f(x,\cdot)$ integrable under each, $0<\beta<1$), suppose that for each $i$ the minimizer set of $F^i_\beta(x,\cdot)$ is $[\underline\alpha^*_i,\overline\alpha^*_i]$, and let
--   $$\mathcal A=\Big[\min_{i\in\mathcal L}\underline\alpha^*_i,\ \max_{i\in\mathcal L}\overline\alpha^*_i\Big].$$
--   Then for every $\lambda\in\Lambda$:
--
--   1. every minimizer of $\alpha\mapsto H_\beta(x,\alpha,\lambda)$ over $\mathbb R$ lies in $\mathcal A$;
--   2. some point of $\mathcal A$ minimizes $H_\beta(x,\cdot,\lambda)$ over $\mathbb R$, so that $\min_{\alpha\in\mathbb R}H_\beta(x,\alpha,\lambda)=\min_{\alpha\in\mathcal A}H_\beta(x,\alpha,\lambda)$.
--
--   This reduces the inner minimization to a compact interval independent of $\lambda$, which is what makes a minimax theorem applicable.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1166, proof of Theorem 1

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem argmin_H_subset {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i))
    (a b : Fin l → ℝ)
    (hab : ∀ i, {α : ℝ | IsMinOn (Fi P f β x i) Set.univ α} = Set.Icc (a i) (b i)) :
    ∀ lam ∈ stdSimplex ℝ (Fin l),
      {α : ℝ | IsMinOn (fun α => Hfun P f β x α lam) Set.univ α} ⊆
          Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
            (Finset.univ.sup' Finset.univ_nonempty b) ∧
        ∃ α₀ ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty a)
            (Finset.univ.sup' Finset.univ_nonempty b),
          IsMinOn (fun α => Hfun P f β x α lam) Set.univ α₀ := by sorry

end WorstCaseCVaR.Mixture
