-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:54:03.256876+00:00
-- url     : https://prove2.me/theorems/eaca12c9-8163-48ed-bf64-8c45ce45785b
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. This supplies the parent’s edge-count conclusion. A proof route is to derive connectedness and triangular faces from maximality, apply Euler’s formula and the face-edge incidence count, then translate the resulting finite edge count to edgeFinset.card. The lower bound of three vertices is essential for the maximal-planar edge formula, and includes the boundary case of a three-vertex triangle. The remaining core obligation is formalizing these planar embedding and face-count arguments from HasPlanarDrawingOn.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) [DecidableRel Q.Adj] (hQ : HasPlanarDrawingOn Q) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ (R : SimpleGraph V) (hRdec : DecidableRel R.Adj), Q ≤ R → HasPlanarDrawingOn R → R ≤ Q) : Q.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
