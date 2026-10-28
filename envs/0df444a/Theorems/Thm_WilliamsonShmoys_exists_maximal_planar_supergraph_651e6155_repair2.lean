-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_651e6155_repair2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_651e6155_repair2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:03:33.714804+00:00
-- url     : https://prove2.me/theorems/f9df33fa-d101-4dc7-88fe-7d38f38a79b4
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_651e6155_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeSet ⊆ M.edgeSet ∧
      (∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N →
        M.edgeSet ⊆ N.edgeSet → N.edgeSet = M.edgeSet) := by sorry
