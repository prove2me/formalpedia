-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_9f0d58b7_b6f9_47f0_b3be_8c258362d568_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_9f0d58b7_b6f9_47f0_b3be_8c258362d568_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:23:36.275706+00:00
-- url     : https://prove2.me/theorems/78fea898-8288-4e1e-a9e5-92d7f51e379d
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   For any graph on a finite linearly ordered vertex type with at least three vertices, if it has a drawing satisfying the given continuous-arc, injectivity, vertex-avoidance, and edge-intersection conditions, then it has a planar supergraph on the same vertex type with exactly 3|V|−6 edges. The proof proceeds by obtaining a finite plane embedding, connecting components as needed, and triangulating faces; Euler's formula supplies the exact count. The argument must preserve all vertices, including isolated ones.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_9f0d58b7_b6f9_47f0_b3be_8c258362d568_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
