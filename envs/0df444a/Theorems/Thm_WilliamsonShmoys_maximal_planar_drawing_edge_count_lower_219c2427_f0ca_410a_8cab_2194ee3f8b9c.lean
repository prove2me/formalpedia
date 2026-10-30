-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_219c2427_f0ca_410a_8cab_2194ee3f8b9c
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_219c2427_f0ca_410a_8cab_2194ee3f8b9c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:21:24.302422+00:00
-- url     : https://prove2.me/theorems/78919b52-de37-4426-ade1-0aaa5522d1e4
-- title:
--   Lower edge bound for an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_219c2427_f0ca_410a_8cab_2194ee3f8b9c
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
