-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_26140903_fcb8_4c7c_a0cc_72edca446c76_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_26140903_fcb8_4c7c_a0cc_72edca446c76_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:39:00.645212+00:00
-- url     : https://prove2.me/theorems/b4563d71-4874-4d4e-af11-bf65d7ec08a5
-- title:
--   Planar triangulation extension has 3n−6 edges
-- statement:
--   Any planar simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a planar graph on the same vertices with exactly 3n−6 edges. This packages the classical triangulation-extension argument. Its proof route augments the drawing inside faces until no further edge can be added, then applies Euler’s formula and the triangular-face property of a maximal planar drawing. The three-vertex case gives the triangle and satisfies the same count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_26140903_fcb8_4c7c_a0cc_72edca446c76_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
