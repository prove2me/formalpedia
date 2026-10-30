-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_completion__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
-- name    : WilliamsonShmoys.planar_drawing_has_edge_maximal_completion__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:09:49.240044+00:00
-- url     : https://prove2.me/theorems/6822b8c0-b310-4ef6-afea-d822182653e7
-- title:
--   Extend a planar drawing to a planar edge-maximal supergraph
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices that admits no strict drawable supergraph. The size hypothesis is retained for the completion theorem’s intended planar setting and includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_edge_maximal_completion__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        (∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by sorry
