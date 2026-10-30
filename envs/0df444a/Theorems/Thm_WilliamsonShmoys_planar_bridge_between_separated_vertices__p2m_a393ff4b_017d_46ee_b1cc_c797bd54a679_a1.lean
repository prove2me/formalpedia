-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_between_separated_vertices__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
-- name    : WilliamsonShmoys.planar_bridge_between_separated_vertices__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:20:34.154868+00:00
-- url     : https://prove2.me/theorems/30c29ada-ff7a-4fa1-8d68-faf97c23b8e0
-- title:
--   Add a drawable bridge between separated vertices
-- statement:
--   Given a drawable finite graph and vertices in different components, there is a drawable supergraph on the same vertices that includes an edge between them. This general bridge lemma removes the target's graph-specific choice of pair and isolates the plane-topology argument. A proof route is to use component face incidence and draw a simple arc in a common face; disconnectedness ensures the chosen endpoints are distinct and nonadjacent. The remaining core obligation is verifying the arc avoids every existing vertex and edge and satisfies the exact continuous-arc drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_bridge_between_separated_vertices__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    {u v : V}
    (huv : ¬ K.Reachable u v) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      M.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
