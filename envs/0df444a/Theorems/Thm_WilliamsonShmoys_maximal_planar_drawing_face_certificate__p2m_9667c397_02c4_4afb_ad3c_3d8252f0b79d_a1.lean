-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_certificate__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_certificate__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:46.302739+00:00
-- url     : https://prove2.me/theorems/f9d76db2-d767-4642-99f4-dff7d260828e
-- title:
--   Face certificate for maximal planar drawings
-- statement:
--   A finite crossing-free drawing of an edge-maximal simple graph with at least three vertices admits a face certificate: its vertex count plus face count is its edge count plus two, the sum of face boundary lengths is twice the edge count, and every face boundary has length three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_face_certificate__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M' : SimpleGraph V, M <= M' ->
      WilliamsonShmoys.HasPlanarDrawingOn M' -> M' = M) :
    Exists (fun f : Nat => Exists (fun len : Fin f -> Nat =>
      (Fintype.card V + f = M.edgeSet.ncard + 2) /\
      (Finset.univ.sum (fun i : Fin f => len i) = 2 * M.edgeSet.ncard) /\
      (forall i : Fin f, len i = 3))) := by
  sorry
