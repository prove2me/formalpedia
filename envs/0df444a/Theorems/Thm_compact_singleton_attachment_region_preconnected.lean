-- Prove2me | Theorems.Thm_compact_singleton_attachment_region_preconnected
-- name    : compact_singleton_attachment_region_preconnected
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T02:46:25.718625+00:00
-- url     : https://prove2.me/theorems/6d14fe2a-3cce-4d89-b9b2-8064a69e1fde
-- title:
--   A one-point nonseparating compact attachment does not split a region
-- statement:
--   Let $K,A\subset\mathbb R^2$ be compact, with $K\cap A$ a singleton, and suppose $\mathbb R^2\setminus A$ is connected or empty. For every point $q\in\mathbb R^2$, let $D$ be the component of $\mathbb R^2\setminus K$ containing $q$ (empty when $q\in K$). Then
--
--   $$D\setminus A$$
--
--   is connected or empty. Thus adding $A$ cannot split an existing complement component of $K$.
-- source:
--   Consequence of Janiszewski’s planar separation theorem; compare the end-cut result cited as Newman, Elements of the Topology of Plane Sets of Points, V.11.6, https://iiscoe.wordpress.com/wp-content/uploads/2020/07/as_triangulation_details-2.pdf . Supports https://prove2.me/theorems/701f7db2-54c5-46ad-a4c7-3073537171ce . Uses Schoenflies plane source files by Álvaro Begué.

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
import Mathlib.Topology.Separation.Regular
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Schoenflies_SquareCycle

open Set

theorem compact_singleton_attachment_region_preconnected
    (K A : Set (ℝ × ℝ)) (p q : ℝ × ℝ) (hK : IsCompact K) (hA : IsCompact A)
    (hinter : K ∩ A = {p}) (hAconn : IsPreconnected Aᶜ) :
    IsPreconnected ((connectedComponentIn Kᶜ q) \ A) := by sorry
