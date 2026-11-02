-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_property_maximal_extension__p2m_e07f1b1a_1ea6_4563_8b26_8f130e22d586_a2
-- name    : WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_e07f1b1a_1ea6_4563_8b26_8f130e22d586_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:52:20.452734+00:00
-- url     : https://prove2.me/theorems/2186e114-f95a-482a-adad-75633b0d132f
-- title:
--   Finite graph property maximal extension
-- statement:
--   For a finite vertex type, if a graph H satisfies a property P and the edge-set cardinalities of all graphs satisfying P have a common finite bound, then H is contained in a P-satisfying graph maximal among P-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_e07f1b1a_1ea6_4563_8b26_8f130e22d586_a2
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V)
    (hH : P H) (B : Nat)
    (hbound : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ B) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by sorry
