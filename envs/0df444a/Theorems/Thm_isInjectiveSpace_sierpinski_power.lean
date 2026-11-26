-- Prove2me | Theorems.Thm_isInjectiveSpace_sierpinski_power
-- name    : isInjectiveSpace_sierpinski_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:29.299713+00:00
-- url     : https://prove2.me/theorems/5d81d56a-3c92-5da2-8467-e96ae5bba45b
-- title:
--   is Injective Space sierpinski power: is Injective Space sierpinski power
-- statement:
--   The is Injective Space sierpinski power construction uses the is Injective Space sierpinski power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L85-L87
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L85-L87

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem isInjectiveSpace_sierpinski_power (ι : Type w) :
    IsInjectiveSpace.{u} (ι → Prop) := by sorry
