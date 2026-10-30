-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar_drawing
-- name    : WilliamsonShmoys.edge_count_of_edge_maximal_planar_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:53:58.389974+00:00
-- url     : https://prove2.me/theorems/32fad0ec-7140-4885-9619-797164807978
-- title:
--   Edge count of an edge-maximal planar drawing
-- statement:
--   A graph on at least three vertices that admits the specified planar drawing and has no proper planar supergraph on the same vertices has exactly 3n−6 edges. The proof must establish the triangulation consequence of edge maximality and apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_edge_maximal_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
