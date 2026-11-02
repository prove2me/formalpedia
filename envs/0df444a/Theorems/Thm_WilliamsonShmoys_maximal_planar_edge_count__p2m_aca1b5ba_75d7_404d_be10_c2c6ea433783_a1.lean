-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_aca1b5ba_75d7_404d_be10_c2c6ea433783_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_aca1b5ba_75d7_404d_be10_c2c6ea433783_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:16:57.556905+00:00
-- url     : https://prove2.me/theorems/f926186e-6933-42b8-b492-59096ed06c95
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   Every inclusion-maximal graph admitting the defined planar drawing, on at least three vertices, has exactly 3n − 6 edges. This removes the maximality-to-triangulation and planar edge-count argument from the parent. A proof route is to show maximality forces triangular faces in a planar embedding and then combine Euler’s formula with the fact that each edge contributes two face sides. The remaining core obligation is formalizing that planar graph argument under the given drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_aca1b5ba_75d7_404d_be10_c2c6ea433783_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : LE.le 3 (Fintype.card V))
    (hMax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    M.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
