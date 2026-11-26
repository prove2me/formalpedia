-- Prove2me | Theorems.Thm_proposition_1_4
-- name    : proposition_1_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:50.726133+00:00
-- url     : https://prove2.me/theorems/130d8ea3-1230-4f13-9e31-dfe9b04b68f5
-- title:
--   proposition 1 4: proposition 1 4
-- statement:
--   The proposition 1 4 construction uses the proposition 1 4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L80-L83
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L80-L83

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem proposition_1_4 {D : Type v} {D' : Type v} [TopologicalSpace D] [TopologicalSpace D']
    (hD : IsInjectiveSpace.{u} D) (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    IsInjectiveSpace.{u} D' := by sorry
