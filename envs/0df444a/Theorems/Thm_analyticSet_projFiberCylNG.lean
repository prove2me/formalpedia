-- Prove2me | Theorems.Thm_analyticSet_projFiberCylNG
-- name    : analyticSet_projFiberCylNG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:01.957525+00:00
-- url     : https://prove2.me/theorems/d4ae35ca-78b4-580e-8ebd-d0bcbccf0950
-- title:
--   analytic Set proj Fiber Cyl NG: analytic Set proj Fiber Cyl NG
-- statement:
--   The analytic Set proj Fiber Cyl NG construction uses the analytic Set proj Fiber Cyl NG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L121-L134
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L121-L134

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem analyticSet_projFiberCylNG [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (f : ℕ → ℕ) (n : ℕ) :
    AnalyticSet (projFiberCylNG F f n) := by sorry
