-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_augmentation_edge_count
-- name    : WilliamsonShmoys.planar_graph_augmentation_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:04:50.328963+00:00
-- url     : https://prove2.me/theorems/a0798f51-6e18-4401-9598-620a32b64bfd
-- title:
--   Planar graph augmentation to the maximal edge count
-- statement:
--   Any drawable simple graph on at least three vertices can be extended, without adding vertices, to a drawable simple graph with exactly 3|V|−6 edges. The child supplies the triangulated completion; the parent’s maximality hypothesis identifies that completion with the original graph, after which the face count follows arithmetically.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_augmentation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
