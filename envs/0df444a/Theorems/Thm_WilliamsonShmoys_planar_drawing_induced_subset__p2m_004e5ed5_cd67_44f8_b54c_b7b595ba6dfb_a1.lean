-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induced_subset__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
-- name    : WilliamsonShmoys.planar_drawing_induced_subset__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:58:09.931649+00:00
-- url     : https://prove2.me/theorems/14ad4541-4bdd-4af6-aa14-469f803bd74d
-- title:
--   Restrict a planar drawing to an induced vertex subset
-- statement:
--   Restricting the vertex points and edge arcs of a drawing to a finite vertex subset gives a drawing of the induced subgraph. This is the bridge from the original drawing to the connected components used in the edge count. The proof route unpacks the drawing witnesses, restricts their domains, and reuses injectivity, continuity, and the intersection conditions. It handles empty and small subsets as well as larger ones.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_induced_subset__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) (S : Finset V) :
    HasPlanarDrawingOn (U.induce (↑S : Set V)) := by sorry
