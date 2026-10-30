-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_30825c49_c1ed_4d16_b870_dd4c24d4c0d7_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_30825c49_c1ed_4d16_b870_dd4c24d4c0d7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:36:22.987006+00:00
-- url     : https://prove2.me/theorems/88eb48a9-1f6f-40de-be2a-bbc9dfe7009a
-- title:
--   Edge bound for a drawable simple graph
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound__p2m_30825c49_c1ed_4d16_b870_dd4c24d4c0d7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
