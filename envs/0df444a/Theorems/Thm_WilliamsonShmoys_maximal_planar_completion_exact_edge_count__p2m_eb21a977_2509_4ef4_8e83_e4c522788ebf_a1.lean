-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_exact_edge_count__p2m_eb21a977_2509_4ef4_8e83_e4c522788ebf_a1
-- name    : WilliamsonShmoys.maximal_planar_completion_exact_edge_count__p2m_eb21a977_2509_4ef4_8e83_e4c522788ebf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:02:48.161907+00:00
-- url     : https://prove2.me/theorems/52c72b1a-727a-4125-917a-c27d4ca055ae
-- title:
--   Drawable graphs admit an exact planar edge-count completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This removes the topological completion and edge-count argument from the parent. A proof route is to extend the drawing to an inclusion-maximal planar graph, show its faces are triangles, and apply Euler’s formula with face-edge incidence counting; when |V|=3, the completion is the triangle. The remaining core obligation is formalizing planar augmentation and the Euler face count for the given arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_completion_exact_edge_count__p2m_eb21a977_2509_4ef4_8e83_e4c522788ebf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
