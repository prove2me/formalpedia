-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_bound
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:28:05.681655+00:00
-- url     : https://prove2.me/theorems/f03d561d-1e05-48e4-985a-a56c82cc8fdc
-- title:
--   Drawable graphs admit a planar supergraph meeting the edge bound
-- statement:
--   Any drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices with at least 3|V|−6 edges. This isolates the planar completion and edge-count argument needed by the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
