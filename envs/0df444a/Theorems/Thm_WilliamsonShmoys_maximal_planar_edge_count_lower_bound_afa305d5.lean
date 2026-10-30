-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_afa305d5
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_afa305d5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:53:12.500001+00:00
-- url     : https://prove2.me/theorems/5c328fac-765a-417b-9efb-796f9de17571
-- title:
--   Lower edge bound for a maximal drawable graph
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex set has at least 3|V| − 6 edges. This supplies the target’s lower bound. The condition |V| ≥ 3 is needed for the triangulation edge count; when |V| = 3, maximality forces the triangle. A proof route is to show maximality rules out nontriangular faces, then count triangular face incidences and apply Euler’s formula. The remaining core is formalizing those planar-topology steps for the given continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_afa305d5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by sorry
