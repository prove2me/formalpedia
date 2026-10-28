-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_exists_maximal_planar_supergraph
-- name    : WilliamsonShmoys.planar_drawingOn_exists_maximal_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:13:12.513999+00:00
-- url     : https://prove2.me/theorems/cb868c2d-a3cd-475f-8e2b-f6b84ebac831
-- title:
--   Maximal planar supergraph on the same vertex set
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has a maximal drawable supergraph on the same vertices, containing its edges and with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_exists_maximal_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
