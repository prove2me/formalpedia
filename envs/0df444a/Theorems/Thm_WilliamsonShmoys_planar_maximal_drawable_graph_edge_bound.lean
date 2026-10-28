-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_drawable_graph_edge_bound
-- name    : WilliamsonShmoys.planar_maximal_drawable_graph_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:51:11.48488+00:00
-- url     : https://prove2.me/theorems/87f04d60-1e18-4262-8bf1-074ce2cba0e4
-- title:
--   An inclusion-maximal drawable graph has the planar edge bound
-- statement:
--   If a drawable simple graph on at least three vertices has no strictly larger drawable supergraph on the same vertices, then it has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_drawable_graph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T →
      R ≤ T → T = R)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ R.edgeSet.ncard := by sorry
