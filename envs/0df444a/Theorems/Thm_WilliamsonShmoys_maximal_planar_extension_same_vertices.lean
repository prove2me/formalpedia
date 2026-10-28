-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_same_vertices
-- name    : WilliamsonShmoys_maximal_planar_extension_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:41:50.37609+00:00
-- url     : https://prove2.me/theorems/cd050b01-9a07-4b9b-9132-918bb6a60ec5
-- title:
--   Extend a drawn graph to a maximal planar supergraph
-- statement:
--   Every connected graph with at least three vertices and a crossing-free drawing has a supergraph on the same vertex set that is maximal among graphs with such drawings; the supergraph has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys_maximal_planar_extension_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hRconn : R.Connected)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      R.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
