-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_bef9e736_66c4_4a44_9d5c_f3c0ae5dba68_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_bef9e736_66c4_4a44_9d5c_f3c0ae5dba68_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:39:44.441231+00:00
-- url     : https://prove2.me/theorems/1585a545-fd39-4184-a40c-5ddea241da05
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph that is inclusion-maximal among drawable graphs on the same vertex type, with at least three vertices, has exactly 3|V|−6 edges. The proof obligation is the topological core: establish connectedness and triangular faces, then combine Euler’s formula with face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_bef9e736_66c4_4a44_9d5c_f3c0ae5dba68_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, M ≤ K → HasPlanarDrawingOn K → K ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
      3 * Fintype.card V = M.edgeFinset.card + 6) := by sorry
