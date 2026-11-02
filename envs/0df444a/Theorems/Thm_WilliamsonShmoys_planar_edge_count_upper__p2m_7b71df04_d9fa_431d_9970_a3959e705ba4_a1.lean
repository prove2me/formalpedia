-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:59:45.186571+00:00
-- url     : https://prove2.me/theorems/c46714b6-9bfd-40bf-95c8-08d778b86369
-- title:
--   Planar edge-count upper bound
-- statement:
--   Any graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has at most `3 |V| - 6` edges. This is the Euler planar edge bound; maximality is not needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
