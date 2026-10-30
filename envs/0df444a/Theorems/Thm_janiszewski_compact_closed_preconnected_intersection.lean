-- Prove2me | Theorems.Thm_janiszewski_compact_closed_preconnected_intersection
-- name    : janiszewski_compact_closed_preconnected_intersection
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T02:54:26.63599+00:00
-- url     : https://prove2.me/theorems/05299868-1f2d-4c98-9bc9-fb657758371c
-- title:
--   Janiszewski’s theorem for a compact set and a closed set
-- statement:
--   Let $S,T\subset\mathbb C$, where $S$ is compact, $T$ is closed, and $S\cap T$ is connected or empty. If $a$ and $b$ belong to the same connected component of both $\mathbb C\setminus S$ and $\mathbb C\setminus T$, then they belong to the same connected component of
--
--   $$\mathbb C\setminus(S\cup T).$$
--
--   This strengthens the compact–compact form of the planar Janiszewski theorem by allowing the second set to be unbounded.
-- source:
--   Isabelle/HOL Analysis, Jordan_Curve, theorem Janiszewski (L. C. Paulson, based on HOL Light), https://www.isabelle.in.tum.de/website-Isabelle2021/dist/library/HOL/HOL-Analysis/Jordan_Curve.html . Also builds on https://prove2.me/theorems/d7e21e1a-922b-437b-9a8c-7e1c8b33180b and the Schoenflies plane source by Álvaro Begué.

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

open Set Metric

theorem janiszewski_compact_closed_preconnected_intersection
    (S T : Set ℂ) (a b : ℂ) (hS : IsCompact S) (hT : IsClosed T)
    (hST : IsPreconnected (S ∩ T))
    (habS : b ∈ connectedComponentIn Sᶜ a)
    (habT : b ∈ connectedComponentIn Tᶜ a) :
    b ∈ connectedComponentIn (S ∪ T)ᶜ a := by sorry
