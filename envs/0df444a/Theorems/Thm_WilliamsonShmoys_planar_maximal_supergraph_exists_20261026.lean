-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists_20261026
-- name    : WilliamsonShmoys.planar_maximal_supergraph_exists_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:37:23.644893+00:00
-- url     : https://prove2.me/theorems/fe9d8202-b29c-4bf6-8aa0-cf74b0ab1d2c
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every finite graph with a drawing as specified has a supergraph on the same vertices that is maximal among planar supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_exists_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧
        ∀ L : SimpleGraph V,
          K' ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K' := by sorry
