-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_f274a542
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_f274a542
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:09:05.127806+00:00
-- url     : https://prove2.me/theorems/97190ecb-eed6-4c6d-af2b-c74cb56610f6
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Among drawable supergraphs of a given finite graph on the same vertex type, one is inclusion-maximal. Choose a drawable supergraph with the greatest edge count; a strict extension would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_f274a542
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  sorry
