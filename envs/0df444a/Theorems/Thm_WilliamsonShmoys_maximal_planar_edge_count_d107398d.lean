-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_d107398d
-- name    : WilliamsonShmoys.maximal_planar_edge_count_d107398d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:17:04.504052+00:00
-- url     : https://prove2.me/theorems/afa305d5-8953-4872-97ad-4ae674439424
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal drawable graph on at least three vertices has exactly 3|V|-6 edges. This removes the topology and Euler-counting work from the parent. The bound includes |V| = 3, where maximality forces a triangle. An independent proof route is to interpret the given arcs as a planar embedding, use maximality to rule out faces whose boundary is not a triangle, and combine triangular-face incidence counting with Euler's formula. The remaining core is formalizing the passage from the continuous drawing predicate to the embedding and face structure.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_d107398d
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
