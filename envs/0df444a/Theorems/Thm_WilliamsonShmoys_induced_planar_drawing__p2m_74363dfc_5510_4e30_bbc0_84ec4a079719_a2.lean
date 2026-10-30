-- Prove2me | Theorems.Thm_WilliamsonShmoys_induced_planar_drawing__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
-- name    : WilliamsonShmoys.induced_planar_drawing__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:06.403574+00:00
-- url     : https://prove2.me/theorems/dcccc5d4-bd4b-4949-aabe-bde593dfad4f
-- title:
--   Planar drawing restricts to induced subgraphs
-- statement:
--   Restrict the vertex locations and edge arcs from a planar drawing of K to the subtype of vertices in s. This removes the geometric existence obligation from the parent reduction. The proof route is to reuse the same location and arc functions, restrict injectivity to the subtype, and observe that every induced edge is already an edge of K, so all continuity and nonintersection conditions inherit. Empty and singleton subsets are covered because the drawing conditions on edges become vacuous as needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.induced_planar_drawing__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (s : Finset V) :
    HasPlanarDrawingOn (K.induce (↑s : Set V)) := by
  sorry
