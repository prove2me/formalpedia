-- Prove2me | Theorems.Thm_finite_nonempty_connected_components_lower_bound__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a2
-- name    : finite_nonempty_connected_components_lower_bound__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:41:50.695702+00:00
-- url     : https://prove2.me/theorems/d17930eb-525d-472a-afdc-c9c0acfd22e8
-- title:
--   A finite nonempty disconnected set has at least two components
-- statement:
--   For a nonempty set with finitely many connected components, disconnectedness forces at least two components. Nonemptiness rules out zero components; a sole connected component would make the set connected. This removes the component-counting step from the parent, leaving the crosscut separation result as the core obligation.
-- source:
--   M. H. A. Newman, Elements of the Topology of Plane Sets of Points, Theorem V.11.7; see its statement at https://iiscoe.wordpress.com/wp-content/uploads/2020/07/as_triangulation_details-2.pdf . Supporting the same-component branch https://prove2.me/theorems/c8030f71-3663-4ed8-be54-5fe08a9e8720 .

import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Set.Card

open Set

theorem finite_nonempty_connected_components_lower_bound__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a2
    (X : Type) [TopologicalSpace X] (s : Set X)
    (hfinite : Finite (ConnectedComponents s)) (hne : s.Nonempty)
    (hdisconnected : ¬ IsConnected s) :
    2 ≤ Nat.card (ConnectedComponents s) := by sorry
