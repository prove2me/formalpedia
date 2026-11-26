-- Prove2me | Theorems.Thm_corollary_1_7
-- name    : corollary_1_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:57.008169+00:00
-- url     : https://prove2.me/theorems/4acab646-2a70-44a6-89d9-3165987eba74
-- title:
--   corollary 1 7: corollary 1 7
-- statement:
--   **Scott 1972, Corollary 1.7.** A space is injective iff it is a retract of every
--   super-space of which it is a subspace.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L121-L132
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L121-L132

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem corollary_1_7 (D : Type u) [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u,u} D ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (e : D → Y), IsEmbedding e →
        ∃ r : C(Y, D), ∀ d, r (e d) = d := by sorry
