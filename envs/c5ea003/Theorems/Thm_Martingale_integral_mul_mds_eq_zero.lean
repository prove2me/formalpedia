-- Prove2me | Theorems.Thm_Martingale_integral_mul_mds_eq_zero
-- name    : Martingale.integral_mul_mds_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T00:04:46.881819+00:00
-- url     : https://prove2.me/theorems/82a775f7-4fc6-46fc-adde-0669160d6e0e
-- title:
--   Orthogonality of martingale increments in $L^2$
-- statement:
--   **Orthogonality of martingale increments.** Let $(\mathcal{F}_j)_{j \ge 0}$ be a filtration on a finite measure space and let $(V_j)_{j\ge0}$ be a square-integrable *martingale difference sequence*: each $V_j$ is $\mathcal{F}_{j+1}$-measurable and $\mathbb{E}[V_j \mid \mathcal{F}_j] = 0$ almost everywhere. Then distinct increments are orthogonal in $L^2$:
--   $$\mathbb{E}[V_i V_j] = 0 \qquad \text{whenever } i < j.$$
--   The proof is the tower property: for $i < j$ the factor $V_i$ is already $\mathcal{F}_j$-measurable, so it can be pulled out of the conditional expectation, giving $\mathbb{E}[V_i V_j \mid \mathcal{F}_j] = V_i\, \mathbb{E}[V_j \mid \mathcal{F}_j] = 0$, and integrating removes the conditioning. This is the mechanism behind every variance computation for martingales — the cross terms in the expansion of a partial sum all vanish — and it is what makes the martingale central limit theorem behave like the independent-summand one.
-- source:
--   D. Williams, Probability with Martingales, Cambridge University Press, 1991, Section 12.1 (orthogonality of martingale increments); R. Durrett, Probability: Theory and Examples, 5th ed., Cambridge University Press, 2019, Theorem 4.4.1 and the orthogonality identity preceding it.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal NNReal

theorem Martingale.integral_mul_mds_eq_zero {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m0) (V : ℕ → Ω → ℝ)
    (hmem : ∀ j, MemLp (V j) 2 μ)
    (hadapt : ∀ j, StronglyMeasurable[ℱ (j + 1)] (V j))
    (hmds : ∀ j, μ[V j | ℱ j] =ᵐ[μ] 0) {i j : ℕ} (hij : i < j) :
    ∫ ω, V i ω * V j ω ∂μ = 0 := by sorry
