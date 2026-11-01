-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawing_face_count__p2m_8d49dd8d_df70_44ed_9374_0df305c3481e_a2
-- name    : WilliamsonShmoys.edge_maximal_drawing_face_count__p2m_8d49dd8d_df70_44ed_9374_0df305c3481e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:26.850196+00:00
-- url     : https://prove2.me/theorems/3649950b-31dd-4927-b1e8-a61f090b394f
-- title:
--   Euler and incidence counts for an edge-maximal planar drawing
-- statement:
--   A finite edge-maximal drawable simple graph on at least three vertices has a face count satisfying Euler’s equation and the triangular-face incidence equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_drawing_face_count__p2m_8d49dd8d_df70_44ed_9374_0df305c3481e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    ∃ f : ℕ,
      Fintype.card V + f = T.edgeFinset.card + 2 ∧
      3 * f = 2 * T.edgeFinset.card := by sorry
