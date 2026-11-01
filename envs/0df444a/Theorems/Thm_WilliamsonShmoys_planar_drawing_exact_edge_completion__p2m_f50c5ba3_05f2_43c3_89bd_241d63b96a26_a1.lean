-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_completion__p2m_f50c5ba3_05f2_43c3_89bd_241d63b96a26_a1
-- name    : WilliamsonShmoys.planar_drawing_exact_edge_completion__p2m_f50c5ba3_05f2_43c3_89bd_241d63b96a26_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:37.762381+00:00
-- url     : https://prove2.me/theorems/258eb918-9051-4673-9031-77873604d1c1
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_exact_edge_completion__p2m_f50c5ba3_05f2_43c3_89bd_241d63b96a26_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       3 * Fintype.card V - 6 = H.edgeFinset.card) := by sorry
