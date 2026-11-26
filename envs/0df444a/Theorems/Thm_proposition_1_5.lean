-- Prove2me | Theorems.Thm_proposition_1_5
-- name    : proposition_1_5
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:28:31.126821+00:00
-- url     : https://prove2.me/theorems/9a1856f3-b633-5101-9e50-4ce4a0cdb173
-- title:
--   proposition 1 5: proposition 1 5
-- statement:
--   **Scott 1972, Proposition 1.5.** Every `T₀`-space embeds into a power of 𝕆, and that
--   power is injective.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L91-L95
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L91-L95

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem proposition_1_5 (X : Type u) [TopologicalSpace X] [T0Space X] :
    IsInjectiveSpace.{u,u} (Opens X → Prop) ∧
      IsEmbedding (productOfMemOpens X) := by sorry
