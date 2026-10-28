-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_c61b3391
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_c61b3391
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:39:27.749994+00:00
-- url     : https://prove2.me/theorems/4121e569-c371-49f5-94ae-97541a850462
-- title:
--   Every finite drawn graph has an edge-maximal planar supergraph
-- statement:
--   Any finite simple graph with a crossing-free drawing is contained, on the same vertex type, in a drawn graph with no strictly larger drawn supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_c61b3391
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V,
          H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
