-- Prove2me | Theorems.Thm_jankov_von_neumann
-- name    : jankov_von_neumann
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:04:02.250152+00:00
-- url     : https://prove2.me/theorems/4a4f0354-0fc7-5f67-ae47-e6f3c4059bfb
-- title:
--   jankov von neumann: jankov von neumann
-- statement:
--   **Jankov–von Neumann Uniformization Theorem** (Kechris 18.1).
--
--   For P analytic in X × Y (Polish spaces), there exists a σ(Σ₁¹)-measurable
--   function φ : X → Y uniformizing P on its projection.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L284-L312
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L284-L312

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

theorem jankov_von_neumann
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y]
    (P : Set (X × Y)) (hP : AnalyticSet P) (hne : P.Nonempty) :
    ∃ (φ : X → Y), AnalyticallyMeasurable φ ∧
      ∀ x ∈ Prod.fst '' P, (x, φ x) ∈ P := by sorry
