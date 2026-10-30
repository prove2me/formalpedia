-- Prove2me | Theorems.Thm_open_region_minus_attached_compact_nonseparator_connected
-- name    : open_region_minus_attached_compact_nonseparator_connected
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T02:55:17.240703+00:00
-- url     : https://prove2.me/theorems/2cf2d557-073e-4d29-a025-47a22e3aeb84
-- title:
--   Removing a compact nonseparator attached along a connected set preserves a region
-- statement:
--   Let $U\subset\mathbb C$ be an open connected set, and let $A\subset\mathbb C$ be compact. Suppose that $\mathbb C\setminus A$ is connected or empty and dense, and that $A\cap(\mathbb C\setminus U)$ is connected or empty. Then
--
--   $$U\setminus A$$
--
--   is nonempty and connected. In particular, removing an end-cut from a planar region preserves connectedness.
-- source:
--   Consequence of the compact–closed Janiszewski theorem in Isabelle/HOL Analysis, Jordan_Curve, https://www.isabelle.in.tum.de/website-Isabelle2021/dist/library/HOL/HOL-Analysis/Jordan_Curve.html ; compare the end-cut theorem attributed to Newman, V.11.6, https://iiscoe.wordpress.com/wp-content/uploads/2020/07/as_triangulation_details-2.pdf . Supports the open crosscut result https://prove2.me/theorems/701f7db2-54c5-46ad-a4c7-3073537171ce .

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

theorem open_region_minus_attached_compact_nonseparator_connected
    (U A : Set ℂ) (hUo : IsOpen U) (hUc : IsConnected U)
    (hAc : IsCompact A) (hAcompl : IsPreconnected Aᶜ) (hAdense : Dense Aᶜ)
    (hinter : IsPreconnected (A ∩ Uᶜ)) :
    IsConnected (U \ A) := by sorry
