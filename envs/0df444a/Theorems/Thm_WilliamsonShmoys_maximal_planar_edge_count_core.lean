-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_core
-- name    : WilliamsonShmoys.maximal_planar_edge_count_core
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:54:00.20499+00:00
-- url     : https://prove2.me/theorems/7369a359-c5f3-4c51-9386-02babbef2a8c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A finite simple graph with at least three vertices that admits the supplied crossing-free drawing and is maximal among drawable supergraphs on the same vertex set has exactly 3n − 6 edges. The case n = 3 gives three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_core
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V, K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
