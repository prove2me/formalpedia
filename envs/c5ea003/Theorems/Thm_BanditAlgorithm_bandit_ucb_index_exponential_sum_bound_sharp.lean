-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_ucb_index_exponential_sum_bound_sharp
-- name    : BanditAlgorithm.bandit_ucb_index_exponential_sum_bound_sharp
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-28T15:50:44.512416+00:00
-- url     : https://prove2.me/theorems/af6c6a48-aa51-4bcb-a8e0-77776d6644fa
-- title:
--   Sharp exponential-sum bound for the UCB counting lemma
-- statement:
--   For $n\in\mathbb{N}$, $\varepsilon>0$, and $a>0$, assign weight $1$ to each $t\le 2a/\varepsilon^2$ and weight
--
--   $$\exp\!\left(-\frac{[t(\varepsilon-\sqrt{2a/t})]^2}{2t}\right)$$
--
--   to each later $t$. The sum of these weights for $1\le t\le n$ is at most $\frac{2}{\varepsilon^2}(a+\sqrt{\pi a}+1)$. This is the sharp, no-extra-$1$ integral comparison used in Lemma 8.2.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Lemma 8.2 and its proof, printed pp. 118–119 / PDF pp. 127–128, https://tor-lattimore.com/downloads/book/book.pdf

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory ProbabilityTheory Real

theorem BanditAlgorithm.bandit_ucb_index_exponential_sum_bound_sharp
    {n : ℕ} {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    Finset.sum (Finset.Icc 1 n) (fun t ↦
      if 2 * a / ε ^ 2 < (t : ℝ) then
        Real.exp (-((t : ℝ) * (ε - Real.sqrt (2 * a / t))) ^ 2 / ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
      else 1) ≤
      2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) := by sorry
