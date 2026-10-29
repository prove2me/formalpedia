-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_simple_graph_has_edge_count_3n_minus_6_19818e22
-- name    : WilliamsonShmoys.maximal_drawable_simple_graph_has_edge_count_3n_minus_6_19818e22
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:58:48.211673+00:00
-- url     : https://prove2.me/theorems/1ef256c2-6154-41ca-a8ba-2b92078fa256
-- title:
--   A maximal drawable graph has the triangular edge count
-- statement:
--   A drawable simple graph on at least three vertices that admits no strict drawable supergraph on the same vertex set has exactly 3|V|−6 edges. The proof must show maximality forces connectedness and triangular faces, then apply Euler’s formula and count face-edge incidences. At three vertices the result is the three edges of K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_simple_graph_has_edge_count_3n_minus_6_19818e22
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
