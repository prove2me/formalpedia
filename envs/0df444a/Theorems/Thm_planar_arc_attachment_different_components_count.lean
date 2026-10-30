-- Prove2me | Theorems.Thm_planar_arc_attachment_different_components_count
-- name    : planar_arc_attachment_different_components_count
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T02:32:51.629114+00:00
-- url     : https://prove2.me/theorems/85942f39-45f0-41ac-9488-2e8f58d792d4
-- title:
--   Attaching an arc between different components preserves the complement count
-- statement:
--   Let $K\subset\mathbb R^2$ be compact, and let $a:[0,1]\to\mathbb R^2$ be continuous and injective. Suppose that $a(0),a(1)\in K$, that the interior of the arc misses $K$, and that its endpoints lie in different connected components of $K$. If $\mathbb R^2\setminus K$ has finitely many components, then the complement of $K\cup a([0,1])$ also has finitely many components and
--
--   $$\#\pi_0\bigl(\mathbb R^2\setminus(K\cup a([0,1]))\bigr)=\#\pi_0(\mathbb R^2\setminus K).$$
--
--   This is the different-endpoint-components case of the arc-attachment component-count theorem.
-- source:
--   Different-component branch of https://prove2.me/theorems/499509f0-5564-4ad2-b052-bdaa0fac6f2b . Uses the classical Janiszewski theorem (1915), as in Robert B. Burckel, An Introduction to Classical Complex Analysis, Vol. 1, Exercise 4.36, https://edu.fjfi.cvut.cz/studijni-materialy/Bc/3.%20rocnik/FKO/Introduction%20to%20complex%20analysis.pdf , and source-checked Schoenflies plane and arc development by Álvaro Begué.

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

theorem planar_arc_attachment_different_components_count
    (K : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hK : IsCompact K) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) (hu : a 0 ∈ K) (hv : a 1 ∈ K)
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hneq : a 1 ∉ connectedComponentIn K (a 0))
    (hfinite : Finite (ConnectedComponents (Kᶜ : Set (ℝ × ℝ)))) :
    Finite (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) =
        Nat.card (ConnectedComponents (Kᶜ : Set (ℝ × ℝ))) := by sorry
