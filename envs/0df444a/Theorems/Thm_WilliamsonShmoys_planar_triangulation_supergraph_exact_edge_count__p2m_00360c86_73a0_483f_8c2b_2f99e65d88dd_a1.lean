-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_00360c86_73a0_483f_8c2b_2f99e65d88dd_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_00360c86_73a0_483f_8c2b_2f99e65d88dd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:47:02.781339+00:00
-- url     : https://prove2.me/theorems/a12109a5-f1ad-4ab6-9c6b-e3b453b2179d
-- title:
--   Planar extension with the maximal planar edge count
-- statement:
--   Any drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_00360c86_73a0_483f_8c2b_2f99e65d88dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
          N.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
