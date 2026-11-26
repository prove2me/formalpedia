-- Prove2me | Theorems.Thm_isInjectiveSpace_sierpinski
-- name    : isInjectiveSpace_sierpinski
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:50.025317+00:00
-- url     : https://prove2.me/theorems/3747f94b-7465-5af1-b368-607125400138
-- title:
--   is Injective Space sierpinski: is Injective Space sierpinski
-- statement:
--   **Scott 1972, Proposition 1.2.** The Sierpiński space is injective.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L42-L49
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L42-L49

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem isInjectiveSpace_sierpinski : IsInjectiveSpace.{u} Prop := by sorry
