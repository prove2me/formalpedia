-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_maximal__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
-- name    : WilliamsonShmoys.planar_drawable_supergraph_maximal__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:04:59.68942+00:00
-- url     : https://prove2.me/theorems/3a2856d1-6f48-41e5-8b30-58e2d90db5c6
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable finite graph on a fixed finite vertex type has an inclusion-maximal drawable supergraph on the same vertices. Finiteness of the set of simple graphs on the vertex type gives a maximal element among drawable supergraphs containing the original graph. The parent uses this to reduce edge counting to the maximal case; the planar drawing and supergraph hypotheses are preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_supergraph_maximal__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V, M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M := by sorry
