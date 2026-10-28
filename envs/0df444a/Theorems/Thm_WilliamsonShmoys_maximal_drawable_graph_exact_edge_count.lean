-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count
-- name    : WilliamsonShmoys.maximal_drawable_graph_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:50:06.631657+00:00
-- url     : https://prove2.me/theorems/dfc91f59-9744-4c9e-839d-8aef265a0a95
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite ordered vertices that has no strict drawable supergraph has exactly 3|V|−6 edges. This removes the Euler-formula and face-triangulation argument from the parent; a proof route is to establish connectedness and triangular faces from maximality, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → False)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
