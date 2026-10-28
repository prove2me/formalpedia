-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on_same_vertices
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:54:40.695746+00:00
-- url     : https://prove2.me/theorems/8616a276-e4bd-430a-999b-182263aec74b
-- title:
--   Maximal planar supergraph on the same vertices
-- statement:
--   Every finite drawable graph with at least three vertices has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
