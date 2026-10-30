-- Prove2me | Theorems.Thm_planar_crosscut_same_complement_component_two_upper__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4
-- name    : planar_crosscut_same_complement_component_two_upper__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:00.911435+00:00
-- url     : https://prove2.me/theorems/1feb8609-3930-4294-9b3f-4606bda421a8
-- title:
--   A crosscut leaves at most two complementary regions
-- statement:
--   The crosscut’s complement in `U` has finitely many connected components, with at most two. This supplies the upper bound and finiteness needed by the parent and the lower-bound child.
-- source:
--   M. H. A. Newman, Elements of the Topology of Plane Sets of Points, Theorem V.11.7; see its statement at https://iiscoe.wordpress.com/wp-content/uploads/2020/07/as_triangulation_details-2.pdf . Supporting the same-component branch https://prove2.me/theorems/c8030f71-3663-4ed8-be54-5fe08a9e8720 .

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Card
import Mathlib.Topology.ContinuousOn

open Set

theorem planar_crosscut_same_complement_component_two_upper__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4
    (U : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1)) (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hinside : a '' Ioo (0 : ℝ) 1 ⊆ U)
    (hzero : a 0 ∈ frontier U) (hone : a 1 ∈ frontier U)
    (hsame : a 1 ∈ connectedComponentIn Uᶜ (a 0)) :
    Finite (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ))) ≤ 2 := by sorry
