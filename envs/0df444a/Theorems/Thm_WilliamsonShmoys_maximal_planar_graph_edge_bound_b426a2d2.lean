-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound_b426a2d2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound_b426a2d2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:35:09.907989+00:00
-- url     : https://prove2.me/theorems/291834bc-7557-4854-abac-cad527f364e5
-- title:
--   An inclusion-maximal planar graph has the Euler edge bound
-- statement:
--   An inclusion-maximal graph satisfying the given planar-drawing predicate, with at least three vertices, has at least 3|V|−6 edges. This includes the equality boundary case |V| = 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

-- The main planar-topology obligation: use maximality to obtain a connected triangulation (handling K₃ at |V|=3), then apply Euler's formula and count face-edge incidences to derive |E| ≥ 3|V|−6. The formalization must work with the specified injective vertex placement and noncrossing arc predicate.

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound_b426a2d2
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ H : SimpleGraph V, U ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ U) :
    3 * Fintype.card V - 6 ≤ U.edgeSet.ncard := by sorry
