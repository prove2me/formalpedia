-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound_from_completion
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_from_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:21:01.945416+00:00
-- url     : https://prove2.me/theorems/53481078-b292-486a-a92c-be0849ecaf94
-- title:
--   Maximal drawable graphs reach the planar edge bound
-- statement:
--   A drawable graph maximal among drawable graphs on the same vertex type has at least 3|V|−6 edges. A proof route completes its drawing to a triangulation on the same vertices; maximality then forces the completion to coincide with M.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_from_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
