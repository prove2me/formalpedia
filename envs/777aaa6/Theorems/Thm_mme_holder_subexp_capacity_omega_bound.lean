-- Prove2me | Theorems.Thm_mme_holder_subexp_capacity_omega_bound
-- name    : mme_holder_subexp_capacity_omega_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T19:07:42.112468+00:00
-- url     : https://prove2.me/theorems/a7ea55fe-018f-4d6b-8344-5d82f8c9d034
-- statement:
--   **The abstract Hölder + subexponential limit lemma.**
--
--   For real $\omega \geq 1$, $V > 1$, $R \geq 1$, if there exists a polynomial-degree $c : \mathbb{R}$ and a sequence of "capacity witnesses" satisfying:
--
--   * the witness summand count $k_N$ is polynomial in $N$ ($k_N \leq (N+1)^c$),
--   * every summand value $x_i$ is nonnegative,
--   * the sum of values exceeds $V^N (1 - \varepsilon)$,
--   * the $\omega$-power sum is bounded by $R^N$,
--
--   then $\omega \cdot \log V \leq \log R$, equivalently $V^\omega \leq R$.
--
--   **Proof outline.** Apply Hölder's inequality with conjugate exponents $(\omega, \omega/(\omega-1))$ to extract $(\sum x_i)^\omega \leq k_N^{\omega-1} \cdot \sum x_i^\omega$. Plug in $\sum x_i \geq V^N (1-\varepsilon)$ and $\sum x_i^\omega \leq R^N$:
--
--   $$V^{N\omega}(1-\varepsilon)^\omega \;\leq\; k_N^{\omega-1} \cdot R^N \;\leq\; \bigl((N+1)^c\bigr)^{\omega-1} \cdot R^N.$$
--
--   Take $N$-th roots: $V^\omega \cdot (1-\varepsilon)^{\omega/N} \leq (N+1)^{c(\omega-1)/N} \cdot R$. As $N \to \infty$, both $(1-\varepsilon)^{\omega/N} \to 1$ and $(N+1)^{c(\omega-1)/N} \to 1$ (polynomial subexp). The infinite-often hypothesis combined with these limits gives $V^\omega \cdot 1 \leq 1 \cdot R$, i.e., $V^\omega \leq R$.
--
--   **The pure real-analysis core of `mme_omega_le_of_subrank_capacity`** (L1-α). Together with `mme_tensorAsymptoticRank_kronPow_le` and the τ-theorem `mme_asymptotic_sum_inequality` (already Proved on platform), this fully discharges the abstract bridge from subrank capacity to ω upper bound.
--
--   **Reusability — fully paper-agnostic.** No tensor, matrix multiplication, or τ-theorem content here; just real analysis on power-mean inequalities. Every future asymptotic-capacity argument (Strassen 1986/1988, CW 1990, Stothers 2010, Vassilevska Williams 2012, Le Gall 2014, Alman–Vassilevska Williams 2020, …) instantiates this leaf with its own $V$, $R$, and witness family.
-- source:
--   https://arxiv.org/abs/2212.11824

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
open Real BigOperators Filter
universe u

theorem mme_holder_subexp_capacity_omega_bound {ω V R : ℝ} (_hω : 1 ≤ ω) (_hV : 1 < V) (_hR : 1 ≤ R) (_hwitness : ∃ c : ℝ, ∀ ε > (0 : ℝ), ∃ᶠ N in Filter.atTop, ∃ (k : ℕ) (x : Fin k → ℝ), (k : ℝ) ≤ (N + 1 : ℝ) ^ c ∧ (∀ i, 0 ≤ x i) ∧ V ^ N * (1 - ε) ≤ ∑ i, x i ∧ ∑ i, (x i) ^ ω ≤ R ^ N) : ω * Real.log V ≤ Real.log R := by sorry
