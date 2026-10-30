-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_for_arcs
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_for_arcs
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:00:09.230367+00:00
-- url     : https://prove2.me/theorems/938ced8b-ed3c-4f4d-804a-3c686007a6cc
-- title:
--   Planar supergraph with the maximal planar edge count
-- statement:
--   Every finite graph with the supplied crossing-free arc drawing and at least three vertices has a planar supergraph on the same vertex set with exactly `3|V| - 6` edges. The parent applies edge-maximality to this supergraph and rewrites its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_count_for_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
