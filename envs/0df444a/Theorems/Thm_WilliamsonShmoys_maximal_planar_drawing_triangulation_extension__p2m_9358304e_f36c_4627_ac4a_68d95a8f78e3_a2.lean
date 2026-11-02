-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension__p2m_9358304e_f36c_4627_ac4a_68d95a8f78e3_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_9358304e_f36c_4627_ac4a_68d95a8f78e3_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:47:02.097749+00:00
-- url     : https://prove2.me/theorems/05b91864-4011-4912-8401-09994d13f3f6
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on that same vertex set whose edge count is $3|V|-6$. This supplies the triangulated supergraph; the parent’s maximality hypothesis then forces it to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_9358304e_f36c_4627_ac4a_68d95a8f78e3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
