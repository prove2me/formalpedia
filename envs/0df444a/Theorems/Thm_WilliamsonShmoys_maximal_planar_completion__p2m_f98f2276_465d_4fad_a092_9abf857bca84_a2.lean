-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion__p2m_f98f2276_465d_4fad_a092_9abf857bca84_a2
-- name    : WilliamsonShmoys.maximal_planar_completion__p2m_f98f2276_465d_4fad_a092_9abf857bca84_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:07:39.49076+00:00
-- url     : https://prove2.me/theorems/1df9add1-a5a1-4f53-ad0d-9ae1cdbe082b
-- title:
--   Triangulated completion of a planar drawing
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three is contained in a graph on the same vertices that has a crossing-free drawing and exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_completion__p2m_f98f2276_465d_4fad_a092_9abf857bca84_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) [DecidableRel H.Adj] (hH : HasPlanarDrawingOn H) (hcard : 3 <= Fintype.card V) : exists (K : SimpleGraph V) (hKdec : DecidableRel K.Adj) (hKfin : Fintype K.edgeSet), (forall u v, H.Adj u v -> K.Adj u v) /\ HasPlanarDrawingOn K /\ 3 * Fintype.card V = (@SimpleGraph.edgeFinset V K hKfin).card + 6 := by sorry
