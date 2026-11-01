-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:00:00.366871+00:00
-- url     : https://prove2.me/theorems/055d45fa-a44d-4012-991d-80fcbbc5becb
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
