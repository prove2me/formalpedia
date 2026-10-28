-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_on_vertices
-- name    : WilliamsonShmoys.exists_planar_supergraph_maximal_on_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:18:09.539696+00:00
-- url     : https://prove2.me/theorems/c9cd2f08-4e78-42af-a5e4-48e0d8275e2a
-- title:
--   A planar graph has a maximal planar supergraph on the same vertices
-- statement:
--   Every finite planar simple graph on at least three vertices is contained in a planar graph on the same vertex set that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_maximal_on_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
