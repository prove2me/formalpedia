-- Prove2me | Theorems.Thm_efron_stein_resampling_variance_identity
-- name    : efron_stein_resampling_variance_identity
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-23T23:36:03.497476+00:00
-- url     : https://prove2.me/theorems/93d518da-42d9-4e6c-9c21-237a4da19b0a
-- statement:
--   **Resampling identity for the variance (Efron–Stein keystone).** Let $W$ and $W'$ be independent, identically distributed, square-integrable real random variables on a probability space. Then
--
--   $$\operatorname{Var}(W) = \tfrac{1}{2}\, \mathbb{E}\big[(W - W')^2\big].$$
--
--   Expanding the square and using independence ($\mathbb{E}[WW'] = \mathbb{E}[W]\,\mathbb{E}[W']$) together with identical distribution ($\mathbb{E}[W] = \mathbb{E}[W']$, $\mathbb{E}[W^2] = \mathbb{E}[W'^2]$) gives $\mathbb{E}[(W-W')^2] = 2(\mathbb{E}[W^2] - (\mathbb{E}W)^2) = 2\operatorname{Var}(W)$. This is the elementary identity underpinning the Efron–Stein inequality via symmetric resampling, and is reusable wherever a resampling argument controls a variance.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550, Princeton), §2.1, proof of Theorem 2.3; Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 3, identity preceding Theorem 3.1.

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem efron_stein_resampling_variance_identity
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {W W' : Ω → ℝ}
    (hW : MemLp W 2 μ) (hW' : MemLp W' 2 μ)
    (hindep : IndepFun W W' μ) (hident : IdentDistrib W W' μ μ) :
    variance W μ = (∫ ω, (W ω - W' ω) ^ 2 ∂μ) / 2 := by sorry
