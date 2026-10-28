-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler
-- name    : WilliamsonShmoys.maximal_planar_edge_count_euler
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:15:25.641981+00:00
-- url     : https://prove2.me/theorems/0576420d-0064-49d4-9582-204b47d32418
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
