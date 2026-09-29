-- Prove2me | Theorems.Thm_max_subgaussian_deviation_union_bound
-- name    : max_subgaussian_deviation_union_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T23:24:06.203249+00:00
-- url     : https://prove2.me/theorems/a1a95d5e-be30-4531-a137-3b402a1cffe4
-- title:
--   Union bound for the maximum of sub-Gaussian variables
-- statement:
--   **Role.** Finite empirical-process supremum concentration via the union bound — the standard first step in controlling $\sup_i |X_i|$ over a finite index set or a finite net, and a reusable building block toward the empirical-process supremum (Talagrand) concentration of exact matrix completion.
--
--   **Claim (maximal sub-Gaussian deviation).** Let $(X_i)_{i\in s}$ be a finite family of real random variables on a probability space, each sub-Gaussian with parameter $c_i$ (`HasSubgaussianMGF (X i) (c i)`). Then for every $\varepsilon\ge 0$,
--   $$\mathbb P\big(\exists\, i\in s,\ |X_i|\ge\varepsilon\big)\ \le\ \sum_{i\in s} 2\exp\!\Big(\frac{-\varepsilon^2}{2c_i}\Big).$$
--   Equivalently, $\mathbb P\big(\max_{i\in s}|X_i|\ge\varepsilon\big)\le\sum_{i\in s}2\exp(-\varepsilon^2/(2c_i))$, and with a uniform parameter $c$ this is $\le 2|s|\exp(-\varepsilon^2/(2c))$.
--
--   **Proof.** The event equals the finite union $\bigcup_{i\in s}\{|X_i|\ge\varepsilon\}$. By the union bound `measureReal_biUnion_finset_le`, its probability is at most $\sum_{i\in s}\mathbb P(|X_i|\ge\varepsilon)$, and each term is bounded by $2\exp(-\varepsilon^2/(2c_i))$ via the two-sided sub-Gaussian tail (one-sided Chernoff `HasSubgaussianMGF.measure_ge_le` applied to $X_i$ and $-X_i$, combined with `measureReal_union_le`).
--
--   **Source.** Standard maximal-inequality union bound for sub-Gaussian variables. R. Vershynin, *High-Dimensional Probability*, CUP 2018, §2.5 (maximum of sub-Gaussians); S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*, OUP 2013, §2.5 (the maximal inequality). Derived from Mathlib's `HasSubgaussianMGF.measure_ge_le` and `measureReal_biUnion_finset_le`.
-- source:
--   Vershynin, High-Dimensional Probability, CUP 2018, §2.5 (maximum of sub-Gaussians); Boucheron-Lugosi-Massart, Concentration Inequalities, OUP 2013, §2.5 (maximal inequality). Union bound (measureReal_biUnion_finset_le) over the two-sided sub-Gaussian tails.

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem max_subgaussian_deviation_union_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {c : ι → ℝ≥0} {s : Finset ι}
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ i ∈ s, ε ≤ |X i ω|}
      ≤ ∑ i ∈ s, 2 * Real.exp (-ε ^ 2 / (2 * c i)) := by sorry
