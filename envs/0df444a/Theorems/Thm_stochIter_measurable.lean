-- Prove2me | Theorems.Thm_stochIter_measurable
-- name    : stochIter_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T08:37:21.258138+00:00
-- url     : https://prove2.me/theorems/e6411bbb-56b3-47c4-8c03-61c5379878b4
-- title:
--   stochIter_measurable
-- statement:
--   Automatically extracted helper theorem stochIter_measurable from oversized parent candidate de37d2acb8f301155d7d44d38261b50b0896da704c8b2f588d0c7ea538d67db4.
-- source:
--   candidate-decomposition:e28554ec-8aa4-49db-8e89-83a73f8c4c8d:de37d2acb8f301155d7d44d38261b50b0896da704c8b2f588d0c7ea538d67db4

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology
open scoped InnerProductSpace
open ShorNonsmooth.Stochastic

theorem stochIter_measurable {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (ℱ : Filtration ℕ m0) (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    Measurable[(ℱ j : MeasurableSpace Ω)] (stochIter h G x₀ j) := by sorry
