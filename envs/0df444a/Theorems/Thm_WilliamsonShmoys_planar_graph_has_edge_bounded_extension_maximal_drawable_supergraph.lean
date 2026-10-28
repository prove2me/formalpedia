-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_bounded_extension_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.planar_graph_has_edge_bounded_extension_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:43:55.255368+00:00
-- url     : https://prove2.me/theorems/fcd8b278-b395-4001-98b4-6bf080aaf57d
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite vertex type has a drawable supergraph maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_edge_bounded_extension_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
