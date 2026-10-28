-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_edge_count_in_finset
-- name    : WilliamsonShmoys.exists_max_edge_count_in_finset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:46:22.916175+00:00
-- url     : https://prove2.me/theorems/99470d9c-4ba0-49da-9260-ffd33317bbfe
-- title:
--   A finite family of finite graphs has a maximum edge count
-- statement:
--   Every nonempty finite family of simple graphs on V contains a graph whose edge count is at least that of every graph in the family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_max_edge_count_in_finset
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Finset (SimpleGraph V)) (hS : S.Nonempty) :
    ∃ H ∈ S, ∀ J ∈ S, J.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
