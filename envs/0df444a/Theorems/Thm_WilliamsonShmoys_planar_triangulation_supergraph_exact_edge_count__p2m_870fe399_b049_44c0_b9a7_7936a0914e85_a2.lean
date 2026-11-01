-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_870fe399_b049_44c0_b9a7_7936a0914e85_a2
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_870fe399_b049_44c0_b9a7_7936a0914e85_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:36.932201+00:00
-- url     : https://prove2.me/theorems/be074bdb-79a8-40c0-b245-62762170066e
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_870fe399_b049_44c0_b9a7_7936a0914e85_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        (letI : DecidableRel K.Adj := dK;
          3 * Fintype.card V - 6 = K.edgeFinset.card) := by sorry
