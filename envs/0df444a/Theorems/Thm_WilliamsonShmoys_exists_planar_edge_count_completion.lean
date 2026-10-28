-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_completion
-- name    : WilliamsonShmoys.exists_planar_edge_count_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T14:07:44.207907+00:00
-- url     : https://prove2.me/theorems/7fab27a5-bdbc-455f-aaf9-3b6b707df05c
-- title:
--   Planar completion with extremal edge count
-- statement:
--   Any finite planar graph on at least three vertices has a planar supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H <= K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
