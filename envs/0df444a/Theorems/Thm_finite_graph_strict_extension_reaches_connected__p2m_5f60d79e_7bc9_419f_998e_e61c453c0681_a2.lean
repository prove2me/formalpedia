-- Prove2me | Theorems.Thm_finite_graph_strict_extension_reaches_connected__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2
-- name    : finite_graph_strict_extension_reaches_connected__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:53.947862+00:00
-- url     : https://prove2.me/theorems/3d85fc57-8a7f-4a4a-b28a-c7b875c3ae9f
-- title:
--   Finite strict extensions reach a connected graph
-- statement:
--   On a finite vertex type, a property-preserving strict edge-set extension step for every disconnected graph satisfying a property can be iterated to a connected graph that still satisfies the property and contains the initial edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_graph_strict_extension_reaches_connected__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hP : P H) (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected → ∃ K : SimpleGraph V, G.edgeSet ⊂ K.edgeSet ∧ P K) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ P K := by sorry
