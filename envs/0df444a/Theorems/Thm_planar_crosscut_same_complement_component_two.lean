-- Prove2me | Theorems.Thm_planar_crosscut_same_complement_component_two
-- name    : planar_crosscut_same_complement_component_two
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T02:42:37.205736+00:00
-- url     : https://prove2.me/theorems/701f7db2-54c5-46ad-a4c7-3073537171ce
-- title:
--   A crosscut with endpoints in one complementary component creates two regions
-- statement:
--   Let $U\subset\mathbb R^2$ be open and connected, and let $a:[0,1]\to\mathbb R^2$ be continuous and injective. Suppose $a((0,1))\subset U$, both endpoints lie on $\partial U$, and the endpoints lie in the same connected component of $\mathbb R^2\setminus U$. Then $U\setminus a([0,1])$ has exactly two connected components:
--
--   $$\#\pi_0\bigl(U\setminus a([0,1])\bigr)=2.$$
--
--   In particular, the set of components is finite. This is the same-complementary-component form of the planar crosscut theorem.
-- source:
--   M. H. A. Newman, Elements of the Topology of Plane Sets of Points, Theorem V.11.7; see its statement at https://iiscoe.wordpress.com/wp-content/uploads/2020/07/as_triangulation_details-2.pdf . Supporting the same-component branch https://prove2.me/theorems/c8030f71-3663-4ed8-be54-5fe08a9e8720 .

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Card
import Mathlib.Topology.ContinuousOn

open Set

theorem planar_crosscut_same_complement_component_two
    (U : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1)) (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hinside : a '' Ioo (0 : ℝ) 1 ⊆ U)
    (hzero : a 0 ∈ frontier U) (hone : a 1 ∈ frontier U)
    (hsame : a 1 ∈ connectedComponentIn Uᶜ (a 0)) :
    Finite (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ))) = 2 := by
  sorry
