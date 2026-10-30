-- Prove2me | Theorems.Thm_finite_connected_components_lower_bound_of_not_connected__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a1
-- name    : finite_connected_components_lower_bound_of_not_connected__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:46.320531+00:00
-- url     : https://prove2.me/theorems/500ab0fd-7125-46e0-8259-170f6e54686b
-- title:
--   A finite component space with a disconnected set has at least two components
-- statement:
--   For any topological space, if a set is disconnected and its connected-component type is finite, that type has cardinality at least two. This removes the component-counting step from the parent. A proof route is to use that connected components partition the set and that a set with at most one component is connected (including the empty-set boundary case, for which `¬ IsConnected s` rules out emptiness).
-- source:
--   M. H. A. Newman, Elements of the Topology of Plane Sets of Points, Theorem V.11.7; see its statement at https://iiscoe.wordpress.com/wp-content/uploads/2020/07/as_triangulation_details-2.pdf . Supporting the same-component branch https://prove2.me/theorems/c8030f71-3663-4ed8-be54-5fe08a9e8720 .

import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Set.Card

open Set

theorem finite_connected_components_lower_bound_of_not_connected__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a1
    (X : Type) [TopologicalSpace X] (s : Set X)
    (hfinite : Finite (ConnectedComponents s)) (hdisconnected : ¬ IsConnected s) :
    2 ≤ Nat.card (ConnectedComponents s) := by sorry
