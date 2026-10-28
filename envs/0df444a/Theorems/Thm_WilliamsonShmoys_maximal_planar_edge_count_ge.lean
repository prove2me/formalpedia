-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ge
-- name    : WilliamsonShmoys.maximal_planar_edge_count_ge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:12:56.512493+00:00
-- url     : https://prove2.me/theorems/2ae4697c-a42a-4710-a005-e9a336142f55
-- title:
--   Maximal planar graph lower bound
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_ge
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V, K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
