-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_with_euler_edge_count
-- name    : WilliamsonShmoys.exists_drawable_supergraph_with_euler_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:45:56.886735+00:00
-- url     : https://prove2.me/theorems/64f89675-3a15-4367-865a-a89cdfffe58e
-- title:
--   Drawable triangulation extension with Euler edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph, on the same vertex set, of a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_drawable_supergraph_with_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
