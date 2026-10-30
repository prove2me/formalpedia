-- Prove2me | Theorems.Thm_planar_crosscut_same_complement_component_two_lower__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4
-- name    : planar_crosscut_same_complement_component_two_lower__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:01.807594+00:00
-- url     : https://prove2.me/theorems/bfad0b38-624c-4f44-b180-c550615568f1
-- title:
--   A crosscut separates into at least two regions
-- statement:
--   Assuming finiteness of the cut complement’s connected components, there are at least two. This is the lower-bound half of the separation result and combines with the upper bound to yield the target.
-- source:
--   M. H. A. Newman, Elements of the Topology of Plane Sets of Points, Theorem V.11.7; see its statement at https://iiscoe.wordpress.com/wp-content/uploads/2020/07/as_triangulation_details-2.pdf . Supporting the same-component branch https://prove2.me/theorems/c8030f71-3663-4ed8-be54-5fe08a9e8720 .

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Card
import Mathlib.Topology.ContinuousOn

open Set

theorem planar_crosscut_same_complement_component_two_lower__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4
    (U : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1)) (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hinside : a '' Ioo (0 : ℝ) 1 ⊆ U)
    (hzero : a 0 ∈ frontier U) (hone : a 1 ∈ frontier U)
    (hsame : a 1 ∈ connectedComponentIn Uᶜ (a 0))
    (hfinite : Finite (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ)))) :
    2 ≤ Nat.card (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ))) := by sorry
