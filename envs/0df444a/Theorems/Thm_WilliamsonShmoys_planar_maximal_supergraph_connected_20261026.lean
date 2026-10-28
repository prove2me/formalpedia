-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_connected_20261026
-- name    : WilliamsonShmoys.planar_maximal_supergraph_connected_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:38:18.136436+00:00
-- url     : https://prove2.me/theorems/b5bfa367-4008-4dce-a7a0-98f3e0567936
-- title:
--   An edge-maximal planar graph is connected
-- statement:
--   A graph with the specified planar drawing that is maximal among its planar supergraphs on the same vertices is connected when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_connected_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hV : 3 ≤ Fintype.card V) :
    K.Connected := by sorry
