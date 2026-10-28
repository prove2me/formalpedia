-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_maximal_drawing_count
-- name    : WilliamsonShmoys.edge_bound_maximal_drawing_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:52:17.275955+00:00
-- url     : https://prove2.me/theorems/81043f4b-2093-41a9-9411-b922a726ecee
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertices has exactly $3|V|-6$ edges. Prove this by showing maximality forces triangular faces, then applying Euler’s formula and counting face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_bound_maximal_drawing_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
