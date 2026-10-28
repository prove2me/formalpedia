-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:16:41.668256+00:00
-- url     : https://prove2.me/theorems/96073b7d-a53d-4e75-b295-88c059c61adb
-- title:
--   Existence of a maximal drawable supergraph for the edge bound
-- statement:
--   Every drawable finite graph has a same-vertex-type drawable supergraph maximal under edge inclusion. Maximizing edge count over the finite set of drawable supergraphs gives an independent proof route: any strict drawable extension would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : Exists fun L : SimpleGraph V => K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L /\ (forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) := by sorry
