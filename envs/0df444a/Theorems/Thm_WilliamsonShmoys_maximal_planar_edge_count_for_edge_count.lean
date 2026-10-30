-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_count
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:17:17.680071+00:00
-- url     : https://prove2.me/theorems/704fa243-4c51-4b56-abae-359fd6febfd9
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly 3n − 6 edges. This isolates the planar topology and face counting needed by the target. A proof route is to use maximality to triangulate the embedding, apply Euler’s formula, and count each edge twice among triangular faces. The child carries nearly all of the parent’s difficulty and is equivalent to its topological core; the parent then follows by choosing f = 2n − 4.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
