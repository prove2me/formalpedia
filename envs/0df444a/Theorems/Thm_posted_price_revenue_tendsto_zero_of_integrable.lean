-- Prove2me | Theorems.Thm_posted_price_revenue_tendsto_zero_of_integrable
-- name    : posted_price_revenue_tendsto_zero_of_integrable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-04T01:38:59.820129+00:00
-- url     : https://prove2.me/theorems/fb17eaf2-b69a-4d1b-9b7b-0760e310a1a3
-- statement:
--   For a buyer-value distribution $\nu$ (finite measure on $\mathbb R$) with a finite first moment, the posted-price revenue $p\cdot\nu([p,\infty))$ tends to $0$ as $p\to\infty$. This is Markov's inequality $p\cdot\nu([p,\infty))\le\int_{[p,\infty)}|v|\,d\nu$ plus dominated convergence; it is the tail-decay input for the existence of an optimal monopoly price.
-- source:
--   Buying to Bundle: Optimal Sourcing from Monopolistic Sellers, Lemmas A.1/C.1 (Sec. 4 / App. C)

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Filter

theorem posted_price_revenue_tendsto_zero_of_integrable
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hint : Integrable (fun v : ℝ => v) ν) :
    Tendsto (fun p : ℝ => p * (ν (Ici p)).toReal) atTop (nhds 0) := by sorry
