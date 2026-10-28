-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_79011c86fe2a4d17
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_79011c86fe2a4d17
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:37:52.732999+00:00
-- url     : https://prove2.me/theorems/9934663a-e288-4541-8797-e551f7cfbe2b
-- title:
--   Lower edge bound for a maximal planar drawing
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex set, with at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_79011c86fe2a4d17
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N <= P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P <= N) :
    3 * Fintype.card V - 6 <= N.edgeSet.ncard := by sorry
