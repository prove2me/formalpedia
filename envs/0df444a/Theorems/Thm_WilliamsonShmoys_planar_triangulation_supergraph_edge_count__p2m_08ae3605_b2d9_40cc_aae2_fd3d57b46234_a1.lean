-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count__p2m_08ae3605_b2d9_40cc_aae2_fd3d57b46234_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_08ae3605_b2d9_40cc_aae2_fd3d57b46234_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:27:08.730044+00:00
-- url     : https://prove2.me/theorems/49e59269-0942-49a7-bb42-8d7dcf799486
-- title:
--   Triangulated supergraph edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|U|−6 edges. This is the extension step needed by the maximality argument; its independent proof requires planar edge augmentation and face counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_08ae3605_b2d9_40cc_aae2_fd3d57b46234_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (H : SimpleGraph U) (hcard : 3 ≤ Fintype.card U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph U, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card U - 6 = K.edgeSet.ncard := by
  sorry
