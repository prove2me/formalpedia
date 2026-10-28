-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_d51190b1_8a07_4935_b1e8_3fdecb95c1b0
-- name    : WilliamsonShmoys.maximal_planar_edge_count_d51190b1_8a07_4935_b1e8_3fdecb95c1b0
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:07:23.056654+00:00
-- url     : https://prove2.me/theorems/f6a933f5-f4d0-46a2-9849-d2be0c6659e1
-- title:
--   Edge count of a maximal graph with a crossing-free drawing
-- statement:
--   A maximal graph admitting the supplied crossing-free drawing, with at least three vertices, has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_d51190b1_8a07_4935_b1e8_3fdecb95c1b0
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
