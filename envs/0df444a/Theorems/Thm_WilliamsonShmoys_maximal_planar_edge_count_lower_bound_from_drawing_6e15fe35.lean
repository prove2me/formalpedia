-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_from_drawing_6e15fe35
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_from_drawing_6e15fe35
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:20:44.514953+00:00
-- url     : https://prove2.me/theorems/93201121-8186-46a0-8982-6b7cb22ea3ad
-- title:
--   Maximality gives the matching planar edge bound
-- statement:
--   A graph maximal among graphs on the same vertex set admitting the specified crossing-free drawing, with at least three vertices, has at least 3n − 6 edges. The standard proof augments it to a triangulation and uses Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_from_drawing_6e15fe35
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → M = N)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
