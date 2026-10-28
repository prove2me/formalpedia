-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_edge_count
-- name    : WilliamsonShmoys.exists_drawable_supergraph_max_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:03:05.447319+00:00
-- url     : https://prove2.me/theorems/1f7e107e-f756-463e-beed-921b500e6190
-- title:
--   A drawable supergraph with maximum edge count
-- statement:
--   Among drawable supergraphs of H on the finite vertex type, there is one whose finite edge set has maximum cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_drawable_supergraph_max_edge_count {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, H ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → Nat.card {e : Sym2 V // e ∈ L.edgeSet} ≤ Nat.card {e : Sym2 V // e ∈ K.edgeSet} := by sorry
