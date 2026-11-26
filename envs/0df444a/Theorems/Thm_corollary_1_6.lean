-- Prove2me | Theorems.Thm_corollary_1_6
-- name    : corollary_1_6
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:28:56.989302+00:00
-- url     : https://prove2.me/theorems/c9058d34-dfe4-457b-9f73-13bf00a10a0c
-- title:
--   corollary 1 6: corollary 1 6
-- statement:
--   **Scott 1972, Corollary 1.6.** Injective spaces are exactly retracts of powers of 𝕆.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L109-L117
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L109-L117

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem corollary_1_6 (D : Type u) [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u,u} D ↔ ∃ (ι : Type u), Nonempty (IsRetractSubspace D (ι → Prop)) := by sorry
