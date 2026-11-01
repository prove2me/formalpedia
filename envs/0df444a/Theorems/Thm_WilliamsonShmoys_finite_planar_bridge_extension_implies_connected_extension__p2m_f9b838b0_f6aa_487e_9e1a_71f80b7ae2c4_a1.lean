-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_bridge_extension_implies_connected_extension__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
-- name    : WilliamsonShmoys.finite_planar_bridge_extension_implies_connected_extension__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:32.36046+00:00
-- url     : https://prove2.me/theorems/379c017c-9b12-41ce-98a9-768da0e93f9a
-- title:
--   Iterate planar component joins to obtain connectedness
-- statement:
--   Suppose every planar supergraph extension of the initial finite graph can be further extended planarly so that any chosen pair of unreachable vertices becomes reachable. Then the initial graph has a connected planar supergraph on the same vertices. The proof iterates the pair-joining property: each step strictly reduces the finite number of reachability classes, and the process stops when the graph is connected. If the initial graph is already connected, no step is needed; the conclusion also covers an empty vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_bridge_extension_implies_connected_extension__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hjoin : ∀ (G : SimpleGraph V), H ≤ G → HasPlanarDrawingOn G →
      ∀ u v : V, ¬ G.Reachable u v →
        ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Reachable u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by sorry
