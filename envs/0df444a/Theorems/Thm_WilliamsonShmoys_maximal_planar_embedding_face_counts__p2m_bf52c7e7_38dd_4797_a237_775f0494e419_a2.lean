-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_embedding_face_counts__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2
-- name    : WilliamsonShmoys.maximal_planar_embedding_face_counts__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:36:46.579811+00:00
-- url     : https://prove2.me/theorems/a731e400-b1bb-4df1-b39d-695b2e00a6cf
-- title:
--   Face counts for a maximal planar drawing
-- statement:
--   For a finite graph with at least three vertices that is maximal among graphs admitting the given crossing-free drawing, there is a face count satisfying Euler’s equation and the triangular face-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_embedding_face_counts__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V) (hMax : forall N : SimpleGraph V, T <= N -> HasPlanarDrawingOn N -> N <= T) : Exists fun f : Nat => And (Fintype.card V + f = T.edgeSet.ncard + 2) (3 * f = 2 * T.edgeSet.ncard) := by sorry
