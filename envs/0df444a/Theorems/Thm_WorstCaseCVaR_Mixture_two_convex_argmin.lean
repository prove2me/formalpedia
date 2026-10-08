-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_two_convex_argmin
-- name    : WorstCaseCVaR.Mixture.two_convex_argmin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:49.921985+00:00
-- url     : https://prove2.me/theorems/77a0f9b8-88a8-4873-bbc0-2e454ad25f1f
-- title:
--   Proof of Theorem 1 — minimizers of $c_1g_1+c_2g_2$ lie in $[\min\{\underline t_1,\underline t_2\},\max\{\overline t_1,\overline t_2\}]$
-- statement:
--   Let $g_1,g_2:\mathbb R\to\mathbb R$ be convex, and suppose the set of minimizers of $g_j$ is the nonempty closed bounded interval $[\underline t_j,\overline t_j]$, $j=1,2$. Let $c_1,c_2\ge0$ with $c_1+c_2>0$. Then $c_1g_1+c_2g_2$ is convex and every minimizer of it lies in
--   $$\big[\min\{\underline t_1,\underline t_2\},\ \max\{\overline t_1,\overline t_2\}\big].$$
--
--   This elementary fact about convex functions on the line localizes the minimizers of positive combinations of the component functions $F^i_\beta$.
--
--   **Formalization Note** The paper calls the weights $\beta_1,\beta_2$; they are renamed $c_1,c_2$ to avoid a clash with the confidence level $\beta$.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1166, proof of Theorem 1

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem two_convex_argmin (g₁ g₂ : ℝ → ℝ)
    (hg₁ : ConvexOn ℝ Set.univ g₁) (hg₂ : ConvexOn ℝ Set.univ g₂)
    (a₁ b₁ a₂ b₂ : ℝ) (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hmin₁ : {t : ℝ | IsMinOn g₁ Set.univ t} = Set.Icc a₁ b₁)
    (hmin₂ : {t : ℝ | IsMinOn g₂ Set.univ t} = Set.Icc a₂ b₂)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc : 0 < c₁ + c₂) :
    ConvexOn ℝ Set.univ (fun t => c₁ * g₁ t + c₂ * g₂ t) ∧
      {t : ℝ | IsMinOn (fun t => c₁ * g₁ t + c₂ * g₂ t) Set.univ t} ⊆
        Set.Icc (min a₁ a₂) (max b₁ b₂) := by sorry

end WorstCaseCVaR.Mixture
