-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_connected_completion__p2m_9c676d6c_6d6d_407a_ad73_9f103d372166_a5
-- name    : WilliamsonShmoys.planar_drawing_disconnected_connected_completion__p2m_9c676d6c_6d6d_407a_ad73_9f103d372166_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:03:35.037447+00:00
-- url     : https://prove2.me/theorems/1255de6e-c2e2-4421-8273-0a953cf555dd
-- title:
--   Connected planar completion of a disconnected drawing
-- statement:
--   A disconnected finite planar drawing on at least three vertices has a connected planar supergraph on the same vertex set with strictly more edges. This child supplies the missing connectivity property in the parent’s disconnected case. Its independent proof route is to redraw the finitely many components in separated regions and join them through faces without crossings until they form one component. The remaining core obligation is to formalize that geometric construction while preserving the drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_disconnected_connected_completion__p2m_9c676d6c_6d6d_407a_ad73_9f103d372166_a5 {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) (hdisc : ¬ K.Connected) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected ∧
      K.edgeSet.ncard < H.edgeSet.ncard := by sorry
