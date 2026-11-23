-- Prove2me | Theorems.Thm_kyprianou82_discountedAt_nonneg
-- name    : kyprianou82_discountedAt_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:32:49.888884+00:00
-- url     : https://prove2.me/theorems/04e392c6-a8f0-4a4e-ae49-9893cb784305
-- title:
--   Discounted first-passage factor is nonnegative
-- statement:
--   A discounted first-passage factor is either zero at an infinite time or a positive real exponential, hence nonnegative for every nonnegative rate.
-- source:
--   Definition of discountedAt for spectrally negative Levy first-passage times.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem kyprianou82_discountedAt_nonneg
    (q : ℝ) (hq : 0 ≤ q) (τ : WithTop ℝ≥0) : 0 ≤ discountedAt q τ := by
  sorry
