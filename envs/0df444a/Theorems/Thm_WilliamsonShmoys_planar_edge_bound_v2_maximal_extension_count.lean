-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_v2_maximal_extension_count
-- name    : WilliamsonShmoys.planar_edge_bound_v2_maximal_extension_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:59:11.142965+00:00
-- url     : https://prove2.me/theorems/05fb8ecf-4c30-4a6b-b16d-2b551d741b67
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A simple planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_v2_maximal_extension_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
