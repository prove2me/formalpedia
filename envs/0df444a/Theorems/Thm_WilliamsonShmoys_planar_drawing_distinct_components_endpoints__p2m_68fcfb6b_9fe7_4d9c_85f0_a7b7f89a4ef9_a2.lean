-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_distinct_components_endpoints__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2
-- name    : WilliamsonShmoys.planar_drawing_distinct_components_endpoints__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T08:14:16.700257+00:00
-- url     : https://prove2.me/theorems/6aa3ad45-7734-4c22-9288-1a9376bb1570
-- title:
--   Select nonadjacent vertices in different components
-- statement:
--   A graph that is not connected has two vertices that are not adjacent and are not reachable from each other.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_drawing_distinct_components_endpoints__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hnc : ¬ K.Connected) :
    ∃ a b : V, ¬ K.Adj a b ∧ ¬ K.Reachable a b := by sorry
