-- Prove2me | Theorems.Thm_compact_planar_arc_face_increment__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
-- name    : compact_planar_arc_face_increment__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:01:53.78497+00:00
-- url     : https://prove2.me/theorems/499509f0-5564-4ad2-b052-bdaa0fac6f2b
-- title:
--   Complement component count under attaching a simple arc to a compact planar set
-- statement:
--   Attaching an injective continuous closed arc to a compact planar set, with its endpoints in the set and its open arc outside, preserves finiteness of complement components. Their number increases by one when the endpoints share a component of the compact set, and otherwise remains unchanged.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Card
import Mathlib.Topology.ContinuousOn

theorem compact_planar_arc_face_increment__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (a : ℝ → ℝ × ℝ)
    (hc : ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hinterior : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t ∉ K)
    (hfinite : Finite (ConnectedComponents {z : ℝ × ℝ // z ∈ Kᶜ})) :
    Finite (ConnectedComponents
      {z : ℝ × ℝ // z ∈ (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ}) ∧
    (a 1 ∈ connectedComponentIn K (a 0) →
      Nat.card (ConnectedComponents
        {z : ℝ × ℝ // z ∈ (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ}) =
      Nat.card (ConnectedComponents {z : ℝ × ℝ // z ∈ Kᶜ}) + 1) ∧
    (a 1 ∉ connectedComponentIn K (a 0) →
      Nat.card (ConnectedComponents
        {z : ℝ × ℝ // z ∈ (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ}) =
      Nat.card (ConnectedComponents {z : ℝ × ℝ // z ∈ Kᶜ})) := by
  sorry
