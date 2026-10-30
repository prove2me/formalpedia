-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_inclusion_maximal_planar_supergraph_e20a9b21
-- name    : WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_supergraph_e20a9b21
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:45:48.53166+00:00
-- url     : https://prove2.me/theorems/dc3302e1-84cf-43b8-aa22-2655fb1d265f
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly 3|V|−6 edges. The lower bound is essential to the usual triangulation edge count and includes the three-vertex triangle case. A proof route is to derive connectedness and triangular faces from maximality, then use Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_supergraph_e20a9b21
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeSet ⊆ M.edgeSet → L.edgeSet = M.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
