-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_edge_bound_count_79011c86fe2a4d17
-- name    : WilliamsonShmoys.planar_maximal_extension_edge_bound_count_79011c86fe2a4d17
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:58:54.602889+00:00
-- url     : https://prove2.me/theorems/2871d07a-e48b-4758-9320-113deb257cd9
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A graph maximal among drawable supergraphs on its vertex set has exactly \(3|V|-6\) edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension_edge_bound_count_79011c86fe2a4d17
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N <= P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P <= N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
