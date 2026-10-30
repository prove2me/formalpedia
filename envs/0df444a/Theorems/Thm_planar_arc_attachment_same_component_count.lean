-- Prove2me | Theorems.Thm_planar_arc_attachment_same_component_count
-- name    : planar_arc_attachment_same_component_count
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T02:33:03.256687+00:00
-- url     : https://prove2.me/theorems/c8030f71-3663-4ed8-be54-5fe08a9e8720
-- title:
--   Attaching an arc within one component adds one complement component
-- statement:
--   Let $K\subset\mathbb R^2$ be compact, and let $a:[0,1]\to\mathbb R^2$ be continuous and injective. Suppose the arc endpoints lie in the same connected component of $K$ and its open arc misses $K$. If $\mathbb R^2\setminus K$ has finitely many components, then the complement of $K\cup a([0,1])$ also has finitely many components and
--
--   $$\#\pi_0\bigl(\mathbb R^2\setminus(K\cup a([0,1]))\bigr)=\#\pi_0(\mathbb R^2\setminus K)+1.$$
--
--   This is the remaining same-endpoint-component case of the original arc-attachment theorem.
-- source:
--   Same-component branch of https://prove2.me/theorems/499509f0-5564-4ad2-b052-bdaa0fac6f2b (compact planar arc attachment). This node is an open obligation in a case-split reduction of that theorem.

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Card
import Mathlib.Topology.ContinuousOn

open Set

theorem planar_arc_attachment_same_component_count
    (K : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hK : IsCompact K) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) (hu : a 0 ∈ K) (hv : a 1 ∈ K)
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hsame : a 1 ∈ connectedComponentIn K (a 0))
    (hfinite : Finite (ConnectedComponents (Kᶜ : Set (ℝ × ℝ)))) :
    Finite (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) =
        Nat.card (ConnectedComponents (Kᶜ : Set (ℝ × ℝ))) + 1 := by
  sorry
