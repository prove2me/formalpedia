-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_eulerData_2026__p2m_43f98bfb_7424_41c7_97de_56fe6ca417c5_a4
-- name    : WilliamsonShmoys.planarDrawingOn_eulerData_2026__p2m_43f98bfb_7424_41c7_97de_56fe6ca417c5_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:34:29.81889+00:00
-- url     : https://prove2.me/theorems/148a33fd-a8c8-45ad-abb1-c64f40036ac1
-- title:
--   Extract Euler and face-incidence data from a planar drawing
-- statement:
--   For a finite simple graph with at least three vertices, convert its crossing-free arc drawing into counts for a connected planar augmentation that preserves the vertices and contains every original edge. The counts satisfy the original-edge bound, Euler's equation, and the face-incidence inequality. This removes the topological argument from the parent, which then derives the edge bound arithmetically. A proof route is to augment the drawing by connecting components and adding edges until it is triangulated, then apply Euler's formula and count edge incidences along face boundaries. The three-vertex lower bound supports the augmentation and face-boundary argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_eulerData_2026__p2m_43f98bfb_7424_41c7_97de_56fe6ca417c5_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ edgeCount faceCount : Nat,
      L.edgeSet.ncard ≤ edgeCount ∧
      Fintype.card V + faceCount = edgeCount + 2 ∧
      3 * faceCount ≤ 2 * edgeCount := by sorry
