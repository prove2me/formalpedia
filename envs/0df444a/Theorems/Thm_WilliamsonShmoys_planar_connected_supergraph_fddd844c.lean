-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_fddd844c
-- name    : WilliamsonShmoys.planar_connected_supergraph_fddd844c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:50:58.66799+00:00
-- url     : https://prove2.me/theorems/2915c18a-a83c-4758-8452-3ab9bb8fd582
-- title:
--   Connected planar extension on the same vertices
-- statement:
--   A finite planar graph on at least three vertices is contained in a connected planar graph on the same vertices, with no fewer edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_supergraph_fddd844c
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      (∀ u v, Nonempty (N.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      (M.edgeSet.ncard : Int) ≤ (N.edgeSet.ncard : Int) := by sorry
