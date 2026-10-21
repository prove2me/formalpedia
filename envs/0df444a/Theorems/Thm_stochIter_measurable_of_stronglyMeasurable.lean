-- Prove2me | Theorems.Thm_stochIter_measurable_of_stronglyMeasurable
-- name    : stochIter_measurable_of_stronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T09:04:27.252638+00:00
-- url     : https://prove2.me/theorems/31db4966-4536-436b-87f9-e5208286ef9e
-- title:
--   stochIter_measurable_of_stronglyMeasurable
-- statement:
--   Automatically extracted helper theorem stochIter_measurable_of_stronglyMeasurable from oversized parent candidate 08f565cbc229a90ee96eb0aeeee6890c2b96e36a6af3a9ee953227573b23522e.
-- source:
--   candidate-decomposition:e28554ec-8aa4-49db-8e89-83a73f8c4c8d:08f565cbc229a90ee96eb0aeeee6890c2b96e36a6af3a9ee953227573b23522e

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology
open scoped InnerProductSpace
open ShorNonsmooth.Stochastic

theorem stochIter_measurable_of_stronglyMeasurable {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (ℱ : Filtration ℕ m0) (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n))
    (hG_meas : ∀ j, StronglyMeasurable[ℱ (j + 1)] (G j)) (j : ℕ) :
    Measurable[(ℱ j : MeasurableSpace Ω)] (stochIter h G x₀ j) := by sorry
