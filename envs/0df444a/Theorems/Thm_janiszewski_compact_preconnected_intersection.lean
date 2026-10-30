-- Prove2me | Theorems.Thm_janiszewski_compact_preconnected_intersection
-- name    : janiszewski_compact_preconnected_intersection
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T02:28:38.981054+00:00
-- url     : https://prove2.me/theorems/d7e21e1a-922b-437b-9a8c-7e1c8b33180b
-- title:
--   Janiszewski’s theorem for compact planar sets
-- statement:
--   Let $S,T\subset\mathbb C$ be compact and suppose $S\cap T$ is connected or empty. Let $a,b\in\mathbb C\setminus(S\cup T)$. If $a$ and $b$ lie in the same connected component of both $\mathbb C\setminus S$ and $\mathbb C\setminus T$, then they lie in the same connected component of
--
--   $$\mathbb C\setminus(S\cup T).$$
--
--   This is the compact planar form of Janiszewski’s separation theorem; the empty-intersection case is included.
-- source:
--   Z. Janiszewski (1915); see Exercise 4.36(ii) and Theorem 4.31 in Robert B. Burckel, An Introduction to Classical Complex Analysis, Vol. 1, https://edu.fjfi.cvut.cz/studijni-materialy/Bc/3.%20rocnik/FKO/Introduction%20to%20complex%20analysis.pdf . Related formal proof: Isabelle/HOL Jordan_Curve, Janiszewski_weak, https://isabelle.in.tum.de/website-Isabelle2017/dist/library/HOL/HOL-Analysis/Jordan_Curve.html . Supporting work for https://prove2.me/theorems/499509f0-5564-4ad2-b052-bdaa0fac6f2b . Uses Schoenflies square-plane source files by Álvaro Begué.

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

theorem janiszewski_compact_preconnected_intersection
    (S T : Set ℂ) (a b : ℂ) (hS : IsCompact S) (hT : IsCompact T)
    (hST : IsPreconnected (S ∩ T)) (ha : a ∉ S ∪ T) (hb : b ∉ S ∪ T)
    (habS : b ∈ connectedComponentIn Sᶜ a)
    (habT : b ∈ connectedComponentIn Tᶜ a) :
    b ∈ connectedComponentIn (S ∪ T)ᶜ a := by sorry
