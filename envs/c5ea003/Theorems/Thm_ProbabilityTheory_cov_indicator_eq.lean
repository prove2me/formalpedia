-- Prove2me | Theorems.Thm_ProbabilityTheory_cov_indicator_eq
-- name    : ProbabilityTheory.cov_indicator_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T00:04:18.390426+00:00
-- url     : https://prove2.me/theorems/b9ab463b-1a10-489a-8fe8-110242f19881
-- title:
--   Covariance of indicators
-- statement:
--   Covariance of two indicators.
--
--   For measurable $A,B$ on a probability space, $\mathrm{Cov}(1_A,1_B)=P(A\cap B)-P(A)P(B)$, since $E[1_A]=P(A)$ and $1_A1_B=1_{A\cap B}$.
--
--   **Formalization Note** Indicators are `Set.indicator` of constant $1$.
-- source:
--   Standard; via covariance_eq_sub and integral_indicator_const

import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

theorem ProbabilityTheory.cov_indicator_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) : cov[Set.indicator A (fun _ => (1 : ℝ)), Set.indicator B (fun _ => (1 : ℝ)); P] = (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal := by sorry
