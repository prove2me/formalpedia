-- Prove2me | Theorems.Thm_compact_obstacle_region_component_equiv
-- name    : compact_obstacle_region_component_equiv
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T03:02:45.611469+00:00
-- url     : https://prove2.me/theorems/f3d0e918-e714-4dc7-a3ee-cb87f4915924
-- title:
--   Complement components of a compact obstacle inside a planar region
-- statement:
--   Let $U\subset\mathbb C$ be a nonempty open connected region, and let $A\subset U$ be compact. There is a bijection between the connected components of $U\setminus A$ and those of $\mathbb C\setminus A$:
--
--   $$\pi_0(U\setminus A)\cong\pi_0(\mathbb C\setminus A).$$
--
--   No finiteness assumption is made. This is the compact-obstacle case of Newman’s component theorem for a closed set contained in a region.
-- source:
--   M. H. A. Newman, Elements of the Topology of Plane Sets of Points, Theorem V.9.3, https://www.scribd.com/document/1006582620/Elements-of-the-Topology-of-Plane-Sets-of-Points-M-H-A-Newman-2d-Ed-Re-set-Cambridge-Eng-Unknown-1964-Cambridge-University-Press . Derived using compact–closed Janiszewski, https://prove2.me/theorems/05299868-1f2d-4c98-9bc9-fb657758371c . Supports the crosscut theorem https://prove2.me/theorems/701f7db2-54c5-46ad-a4c7-3073537171ce .

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_Schoenflies_Bounded
import Definitions.Def_Schoenflies_Graph_OuterFace
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set

theorem compact_obstacle_region_component_equiv (U A : Set ℂ) (hUo : IsOpen U) (hUc : IsConnected U)
    (hAc : IsCompact A) (hAU : A ⊆ U) :
    Nonempty (ConnectedComponents ((U \ A) : Set ℂ) ≃ ConnectedComponents (Aᶜ : Set ℂ)) := by sorry
