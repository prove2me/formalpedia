-- Prove2me | Theorems.Thm_closedUniformizerG_cylinder_eq
-- name    : closedUniformizerG_cylinder_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:13.545731+00:00
-- url     : https://prove2.me/theorems/593bf846-5546-42c3-98ac-bf537da0e28e
-- title:
--   closed Uniformizer G cylinder eq: closed Uniformizer G cylinder eq
-- statement:
--   The closed Uniformizer G cylinder eq construction uses the closed Uniformizer G cylinder eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L150-L222
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L150-L222

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

theorem closedUniformizerG_cylinder_eq [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty)
    (f : ℕ → ℕ) (n : ℕ) :
    { x | ∀ i < n, closedUniformizerG F hF hne x i = f i } =
      (projFiberCylNG F f n ∩
        ⋂ (m : Fin n), ⋂ (j : Fin (f m)),
          (projFiberCylNG F (Function.update f m j) (↑m + 1))ᶜ) ∪
      ((Prod.fst '' F)ᶜ ∩ { _x | ∀ i < n, hne.some.2 i = f i }) := by sorry
