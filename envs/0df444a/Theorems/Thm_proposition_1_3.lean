-- Prove2me | Theorems.Thm_proposition_1_3
-- name    : proposition_1_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:50.696824+00:00
-- url     : https://prove2.me/theorems/ddd7a8ce-02f4-425a-bcea-a0ca6ae7c4e2
-- title:
--   proposition 1 3: proposition 1 3
-- statement:
--   The proposition 1 3 construction uses the proposition 1 3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L64-L66
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L64-L66

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem proposition_1_3 {ι : Type w} (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    (h : ∀ i, IsInjectiveSpace.{u} (D i)) : IsInjectiveSpace.{u} (∀ i, D i) := by sorry
