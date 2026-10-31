-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_supergraph__p2m_12adc1a9_2da3_4bce_a578_d16f94d48e85_a1
-- name    : WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_12adc1a9_2da3_4bce_a578_d16f94d48e85_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:19:04.148054+00:00
-- url     : https://prove2.me/theorems/db945aeb-851f-483a-bea1-5475ecdeebb9
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_12adc1a9_2da3_4bce_a578_d16f94d48e85_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
