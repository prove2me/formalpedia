-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_bounded_extension
-- name    : WilliamsonShmoys.planar_graph_has_edge_bounded_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:28:57.096117+00:00
-- url     : https://prove2.me/theorems/b35b9526-2968-4401-ac87-aad8a3580ca5
-- title:
--   Planar graph extension with the planar edge lower bound
-- statement:
--   Every finite graph with at least three vertices that has a crossing-free drawing admits a drawable supergraph on the same vertex set with at least 3|V|−6 edges. This is the extension step that lets maximality force the original graph to attain the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_edge_bounded_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
