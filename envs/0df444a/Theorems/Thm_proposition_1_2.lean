-- Prove2me | Theorems.Thm_proposition_1_2
-- name    : proposition_1_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:12.589283+00:00
-- url     : https://prove2.me/theorems/c6e29a1b-db1f-4c16-b0e8-27786ec96b71
-- title:
--   proposition 1 2: proposition 1 2
-- statement:
--   The proposition 1 2 construction uses the proposition 1 2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L51-L52
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L51-L52

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem proposition_1_2 : IsInjectiveSpace.{u} Sierpinski := by sorry
