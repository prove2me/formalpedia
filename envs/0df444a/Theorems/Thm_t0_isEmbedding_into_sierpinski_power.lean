-- Prove2me | Theorems.Thm_t0_isEmbedding_into_sierpinski_power
-- name    : t0_isEmbedding_into_sierpinski_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:54.924001+00:00
-- url     : https://prove2.me/theorems/93b8de9b-e99c-4553-9303-17a8cc60f787
-- title:
--   t0 is Embedding into sierpinski power: t0 is Embedding into sierpinski power
-- statement:
--   The t0 is Embedding into sierpinski power construction uses the t0 is Embedding into sierpinski power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L97-L99
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L97-L99

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem t0_isEmbedding_into_sierpinski_power (X : Type u) [TopologicalSpace X] [T0Space X] :
    IsEmbedding (productOfMemOpens X) := by sorry
