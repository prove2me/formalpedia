-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:34:24.392271+00:00
-- url     : https://prove2.me/theorems/bd57f3c8-e371-4c77-9b1f-383221a33d80
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   For a finite simple graph on at least three vertices with a crossing-free drawing, the edge count is at most 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
